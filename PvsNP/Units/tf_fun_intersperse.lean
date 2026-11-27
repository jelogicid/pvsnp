import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_inv_hom_closed

set_option autoImplicit false

/-
Writing `false` between the bits of a binary string takes polynomial time (TM2).

The identity this file rests on is a plain list equality:

    x.intersperse false = (x.flatMap fun b => [false, b]).tail

The settled unit `m2_inv_hom_closed` proves that `x ↦ x.flatMap h` is computable in polynomial
time for any `h : Bool → List Bool` (`cpt_flatMap`), and the settled unit `fr_ladner` proves that
`List.tail` is computable in polynomial time (`cpt_tail`) and that polynomial-time computable
functions compose (`cpt_comp`). Instantiating `h` at `fun b => [false, b]` and composing with
`List.tail` gives this unit's function.

Every proof below is written for this file; nothing is copied.
-/

namespace PvsNP.Units.tf_fun_intersperse_aux

/-- The list identity the whole proof rests on: interspersing `false` is the same as
flat-mapping each bit to `[false, b]` and dropping the leading `false` that produces. -/
theorem intersperse_eq_tail_flatMap (x : List Bool) :
    x.intersperse false = (x.flatMap fun b => [false, b]).tail := by
  induction x with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      show a :: false :: (b :: t').intersperse false
          = ([false, a] ++ ([false, b] ++ List.flatMap (fun b => [false, b]) t')).tail
      rw [ih]
      rfl

end PvsNP.Units.tf_fun_intersperse_aux

theorem PvsNP.Units.tf_fun_intersperse :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.intersperse false) := by
  have hflat :
      PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => x.flatMap fun b => [false, b]) :=
    PvsNP.Units.m2_inv_hom_closed.cpt_flatMap (fun b => [false, b])
  have htail :
      PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun s : List Bool => s.tail) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail
  have hcomp :
      PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => (x.flatMap fun b => [false, b]).tail) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hflat htail
  have hcongr :
      PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => x.intersperse false) := by
    rw [funext (fun x => PvsNP.Units.tf_fun_intersperse_aux.intersperse_eq_tail_flatMap x)]
    exact hcomp
  exact hcongr
