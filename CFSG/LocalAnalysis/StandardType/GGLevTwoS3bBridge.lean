module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

theorem levTwoS3b_isRt_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {v : ι → ℤ} (hv : IsRt hR v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨w, j, hw⟩ := hv
  have hform := form_weylAction hR w (Pi.single j 1) (Pi.single j 1)
  rw [hw, toRat_single, form_single_single, map_zero] at hform
  have h0 : form hR (0 : ι → ℚ) (0 : ι → ℚ) = 0 := by simp
  rw [h0] at hform
  have := symmetrizer_pos hR j
  linarith

theorem levTwoS3b_weylAction_rRefl_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℤ} {hR : TauCeti.IsFiniteType R} {v : ι → ℤ} (hv : IsRt hR v) :
    weylAction hR (rRefl hR v) v = -v := by
  obtain ⟨k, hk, hw⟩ := weylAction_rRefl hR hv v
  have hpos : form hR (toRat v) (toRat v) ≠ 0 := by
    refine ne_of_gt (form_pos hR ?_)
    intro h
    exact levTwoS3b_isRt_ne_zero hv (toRat_injective (h.trans (map_zero toRat).symm))
  have hk2 : k = 2 := by
    have h : ((k : ℚ) - 2) * form hR (toRat v) (toRat v) = 0 := by linarith
    have h' : (k : ℚ) - 2 = 0 := (mul_eq_zero.mp h).resolve_right hpos
    have h'' : (k : ℚ) = 2 := by linarith
    exact_mod_cast h''
  rw [hw, hk2]
  module

theorem levTwoS3b_testBit_one_shiftLeft (c i : ℕ) : (1 <<< c).testBit i = true ↔ i = c := by
  rw [show (1 : ℕ) <<< c = 2 ^ c by simp [Nat.shiftLeft_eq], Nat.testBit_two_pow]
  simp [eq_comm]

@[expose] def levTwoS3b_foldStep (acc : ℕ × List ℕ) (c : ℕ) : ℕ × List ℕ :=
  if acc.1.testBit c then acc else (acc.1 ||| (1 <<< c), c :: acc.2)

theorem levTwoS3b_foldl_inv {P : ℕ → Prop} (l : List ℕ) (v : ℕ) (q : List ℕ)
    (hP : ∀ i ∈ l, P i) (hv : ∀ i, v.testBit i = true → P i) (hq : ∀ i ∈ q, P i) :
    (∀ i, (l.foldl levTwoS3b_foldStep (v, q)).1.testBit i = true → P i) ∧
      (∀ i ∈ (l.foldl levTwoS3b_foldStep (v, q)).2, P i) := by
  induction l generalizing v q with
  | nil => exact ⟨hv, hq⟩
  | cons c l ih =>
      rw [List.foldl_cons]
      by_cases hc : v.testBit c
      · simp only [levTwoS3b_foldStep, hc, if_true]
        exact ih v q (fun i hi => hP i (List.mem_cons_of_mem c hi)) hv hq
      · simp only [levTwoS3b_foldStep, hc]
        refine ih (v ||| (1 <<< c)) (c :: q) (fun i hi => hP i (List.mem_cons_of_mem c hi)) ?_ ?_
        · intro i hi
          rw [Nat.testBit_lor, Bool.or_eq_true] at hi
          rcases hi with hi | hi
          · exact hv i hi
          · rw [levTwoS3b_testBit_one_shiftLeft] at hi
            simpa [hi] using hP c List.mem_cons_self
        · intro i hi
          rcases List.mem_cons.mp hi with hi | hi
          · simpa [hi] using hP c List.mem_cons_self
          · exact hq i hi

@[expose] def levTwoS3b_bfsMask (perms : List (List ℕ)) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, vis => vis
  | _ + 1, [], vis => vis
  | f + 1, i :: rest, vis =>
      let r := (perms.map (fun p => p.getD i 0)).foldl levTwoS3b_foldStep (vis, [])
      levTwoS3b_bfsMask perms f (rest ++ r.2) r.1

theorem levTwoS3b_Cl_of_bfsMask {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (ι → ℤ)} {S : Set (ι → ℤ)} {perms : List (List ℕ)}
    (hperm : ∀ p ∈ perms, ∀ i, Cl hR S (roots.getD i 0) → Cl hR S (roots.getD (p.getD i 0) 0)) :
    ∀ (fuel : ℕ) (q : List ℕ) (vis : ℕ),
      (∀ i ∈ q, Cl hR S (roots.getD i 0)) →
      (∀ i, vis.testBit i = true → Cl hR S (roots.getD i 0)) →
      ∀ i, (levTwoS3b_bfsMask perms fuel q vis).testBit i = true → Cl hR S (roots.getD i 0) := by
  intro fuel
  induction fuel with
  | zero => intro q vis _ hvis i hi; exact hvis i hi
  | succ f ih =>
      intro q vis hq hvis
      cases q with
      | nil => intro i hi; exact hvis i hi
      | cons b rest =>
          simp only [levTwoS3b_bfsMask]
          obtain ⟨hr1, hr2⟩ := levTwoS3b_foldl_inv (perms.map (fun p => p.getD b 0)) vis []
            (fun i hi => by
              obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
              exact hperm p hp b (hq b List.mem_cons_self))
            hvis (fun i hi => by simp at hi)
          exact ih _ _ (fun i hi => by
            rcases List.mem_append.mp hi with hi | hi
            · exact hq i (List.mem_cons_of_mem b hi)
            · exact hr2 i hi) hr1

end CFSG.StandardType.LevTwo
