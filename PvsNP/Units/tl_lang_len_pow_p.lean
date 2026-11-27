import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

/-
The strings whose length is a perfect cube are in P (TM2).

The machine keeps a counter `k` (written unary, `true` repeated) and one flag saying whether a
cube of the length it has passed matched. One step advances the counter and recomputes
`k * k * k`, comparing it to `|x|` by the length comparison the settled `fr_ladner` supplies. After
`|x| + 1` steps the counter has covered `0 .. |x|`, which holds every cube root the length can
have, so the flag says exactly whether `|x|` is a cube.

The proof shape follows the campaign's own settled `tl_lang_len_square_p`, one power up: the
counter and the flag are the same, `mulU k (mulU k k)` replaces `mulU k k`, and the arithmetic
identity is `(k * k) * k = k ^ 3`.

Nothing is copied; the step, its bound, the run and the arithmetic are written here.
-/

namespace PvsNP.Units.tl_lang_len_pow_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-- `k` cubed, written in unary: `k * k` then that times `k`. -/
def cubeU (k : List Bool) : List Bool := mulU k (mulU k k)

/-- One step: advance the counter, recompute the cube, set the flag when it matches `|x|`. -/
def cubeStep (s : List Bool) : List Bool :=
  let k := (unpairB s).1
  let fnd := (unpairB (unpairB s).2).1
  let x := (unpairB (unpairB s).2).2
  let c := cubeU k
  let eqF := sel (leFlag c x) [] (sel (leFlag x c) [] [true])
  let fnd' := sel fnd eqF [true]
  pairB (true :: k) (pairB fnd' x)

theorem cpt_cubeU :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cubeU := by
  have hk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun k : List Bool => k) := cpt_id
  have hsq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun k : List Bool => mulU k k) := cpt_mulU2 hk hk
  exact cpt_mulU2 hk hsq

theorem cpt_cubeStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cubeStep := by
  have hk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hfnd : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (unpairB s).1 (mulU (unpairB s).1 (unpairB s).1)) := by
    have hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun s => mulU (unpairB s).1 (unpairB s).1) := cpt_mulU2 hk hk
    exact cpt_mulU2 hk hs
  have heqF := cpt_sel (cpt_leFlag hc hx) (cpt_const [])
    (cpt_sel (cpt_leFlag hx hc) (cpt_const []) (cpt_const [true]))
  have hfnd' := cpt_sel hfnd heqF (cpt_const [true])
  exact cpt_pairB2 (cpt_cons1 true hk) (cpt_pairB2 hfnd' hx)

theorem cubeU_length (k : List Bool) : (cubeU k).length = k.length * k.length * k.length := by
  simp [cubeU, mulU, Nat.mul_assoc]

theorem cubeStep_length (s : List Bool) : (cubeStep s).length ≤ s.length + 6 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have heqF : (sel (leFlag (cubeU (unpairB s).1) (unpairB (unpairB s).2).2) []
      (sel (leFlag (unpairB (unpairB s).2).2 (cubeU (unpairB s).1)) [] [true])).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  have hfnd' : (sel (unpairB (unpairB s).2).1
      (sel (leFlag (cubeU (unpairB s).1) (unpairB (unpairB s).2).2) []
        (sel (leFlag (unpairB (unpairB s).2).2 (cubeU (unpairB s).1)) [] [true])) [true]).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  simp only [cubeStep, pairB_length, List.length_cons]
  omega

theorem eqFlag_eq (a b : List Bool) :
    sel (leFlag a b) [] (sel (leFlag b a) [] [true]) =
      if a.length = b.length then [true] else [] := by
  unfold sel leFlag
  by_cases h1 : a.length ≤ b.length <;> by_cases h2 : b.length ≤ a.length
  · have heq : a.length = b.length := by omega
    simp [h1, h2, heq]
  · have hne : a.length ≠ b.length := by omega
    simp [h1, h2, hne]
  · have hne : a.length ≠ b.length := by omega
    simp [h1, h2, hne]
  · omega

/-- After `n` steps the flag holds exactly that some `j < n` had `(k₀ + j) ^ 3 = |x|`. -/
theorem cubeStep_iter_iff (n : ℕ) (k₀ fnd₀ x : List Bool) (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    (unpairB (unpairB (cubeStep^[n] (pairB k₀ (pairB fnd₀ x)))).2).1 = [true] ↔
      (fnd₀ = [true] ∨ ∃ j < n, (k₀.length + j) ^ 3 = x.length) := by
  induction n generalizing k₀ fnd₀ with
  | zero => simp [unpairB_pairB]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : cubeStep (pairB k₀ (pairB fnd₀ x)) =
        pairB (true :: k₀) (pairB
          (sel fnd₀ (if (cubeU k₀).length = x.length then [true] else []) [true]) x) := by
      simp only [cubeStep, unpairB_pairB, eqFlag_eq]
    rw [hstep]
    let fnd' := sel fnd₀ (if (cubeU k₀).length = x.length then [true] else []) [true]
    have hfnd' : fnd' = [] ∨ fnd' = [true] := by
      dsimp [fnd']; unfold sel; split_ifs <;> simp
    rw [ih (true :: k₀) fnd' hfnd']
    have hcube : (cubeU k₀).length = k₀.length ^ 3 := by
      rw [cubeU_length]; ring
    have hfnd'_iff : fnd' = [true] ↔ (fnd₀ = [true] ∨ k₀.length ^ 3 = x.length) := by
      dsimp [fnd']; unfold sel
      rcases hfnd with rfl | rfl
      · simp [hcube]
      · simp
    rw [hfnd'_iff, List.length_cons]
    constructor
    · rintro ((h0 | hsq) | ⟨j, hj, hjsq⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨0, Nat.succ_pos m, by simpa using hsq⟩
      · exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by convert hjsq using 2; omega⟩
    · rintro (h0 | ⟨j, hj, hjsq⟩)
      · exact Or.inl (Or.inl h0)
      · cases j with
        | zero => exact Or.inl (Or.inr (by simpa using hjsq))
        | succ j' => exact Or.inr ⟨j', Nat.lt_of_succ_lt_succ hj, by convert hjsq using 2; omega⟩

/-- The flag is always `[]` or `[true]`, so its emptiness decides it. -/
theorem cubeStep_iter_or (n : ℕ) (k₀ fnd₀ x : List Bool) (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    let r := (unpairB (unpairB (cubeStep^[n] (pairB k₀ (pairB fnd₀ x)))).2).1
    r = [] ∨ r = [true] := by
  induction n generalizing k₀ fnd₀ with
  | zero => simpa [unpairB_pairB] using hfnd
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : cubeStep (pairB k₀ (pairB fnd₀ x)) =
        pairB (true :: k₀) (pairB
          (sel fnd₀ (if (cubeU k₀).length = x.length then [true] else []) [true]) x) := by
      simp only [cubeStep, unpairB_pairB, eqFlag_eq]
    rw [hstep]
    let fnd' := sel fnd₀ (if (cubeU k₀).length = x.length then [true] else []) [true]
    have hfnd' : fnd' = [] ∨ fnd' = [true] := by
      dsimp [fnd']; unfold sel; split_ifs <;> simp
    exact ih (true :: k₀) fnd' hfnd'

def nonEmptyD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, some true)
  | true, _ => (true, none)

theorem cpt_nonEmpty :
    ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodeAnswer
      (fun l : List Bool => !l.isEmpty) := by
  refine fst_polyTime _ _ _ nonEmptyD (fun q => if q then none else some false) false ?_
  intro l
  have htrue : ∀ t : List Bool,
      fstRun nonEmptyD (fun q => if q then none else some false) true t = [] := by
    intro t; induction t with | nil => rfl | cons _ _ ih => simp [fstRun, nonEmptyD, ih]
  cases l with
  | nil => rfl
  | cons b t => simp [PvsNP.encodeAnswer, Computability.encodeBool, fstRun, nonEmptyD, htrue]

end PvsNP.Units.tl_lang_len_pow_p

theorem PvsNP.Units.tl_lang_len_pow_p :
    ({x : List Bool | ∃ k : ℕ, x.length = k ^ 3} : Language Bool) ∈ PvsNP.P := by
  have hInit : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
  have hIter := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_iterGrow
    PvsNP.Units.tl_lang_len_pow_p.cpt_cubeStep 6
    PvsNP.Units.tl_lang_len_pow_p.cubeStep_length
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_cons1 true
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
    hInit
  have hFnd := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hIter
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB1_1
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2)
  have hDec := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hFnd
    PvsNP.Units.tl_lang_len_pow_p.cpt_nonEmpty
  refine ⟨_, hDec, ?_⟩
  intro x
  change (∃ k : ℕ, x.length = k ^ 3) ↔
    (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_pow_p.cubeStep^[(true :: x).length]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1.isEmpty) = true
  simp only [List.length_cons]
  have hiff := PvsNP.Units.tl_lang_len_pow_p.cubeStep_iter_iff (x.length + 1) [] [] x (Or.inl rfl)
  have hor := PvsNP.Units.tl_lang_len_pow_p.cubeStep_iter_or (x.length + 1) [] [] x (Or.inl rfl)
  simp only [List.length_nil, zero_add] at hiff
  have hiff' : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_pow_p.cubeStep^[x.length + 1]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1 = [true] ↔
      ∃ j < x.length + 1, j ^ 3 = x.length := by
    rw [hiff]
    constructor
    · rintro (h | h)
      · exact absurd h (by simp)
      · exact h
    · exact Or.inr
  have hne : (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tl_lang_len_pow_p.cubeStep^[x.length + 1]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1.isEmpty) = true ↔
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.tl_lang_len_pow_p.cubeStep^[x.length + 1]
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x)))).2).1 = [true] := by
    rcases hor with h | h <;> rw [h] <;> simp
  rw [hne, hiff']
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk.symm⟩
    have hle : k ≤ k ^ 3 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · have h1 : 1 ≤ k := h
        have h2 : k * 1 ≤ k * k := Nat.mul_le_mul_left k h1
        have h3 : k ^ 3 = k * k * k := by ring
        rw [h3]
        nlinarith
    omega
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj.symm⟩
