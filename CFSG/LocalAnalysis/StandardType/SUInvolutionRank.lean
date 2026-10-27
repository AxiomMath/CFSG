module

public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSU
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSUDiag
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.StandardType.SUTransvection

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

omit [CharP F 2] in
private lemma ggInvUDiag_eq_diagonal (n l : ℕ) :
    ggInvUDiag n l F = diagonal (fun i : Fin n => if (i : ℕ) < l then (1 : F) else 0) := by
  ext a b
  by_cases h : a = b <;> simp [ggInvUDiag, Matrix.diagonal, h]

omit [CharP F 2] in
theorem rank_ggInvUNil {l : ℕ} (h : 2 * l ≤ n) : (ggInvUNil n l F).rank = l := by
  classical
  rw [← Matrix.rank_mul_eq_right_of_det_ne_zero (antidiag n) (ggInvUNil n l F)
    (det_antidiag_ne_zero n), antidiag_mul_ggInvUNil h, ggInvUDiag_eq_diagonal,
    Matrix.rank_diagonal, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun i : Fin n =>
      (if (i : ℕ) < l then (1 : F) else 0) ≠ 0) =
      Finset.univ.filter fun i : Fin n => (i : ℕ) < l := by
    ext i
    simp
  rw [hfilter, Fin.card_filter_val_lt, min_eq_right (by omega)]

omit [CharP F 2] in
theorem rank_mat_conj_sub_one (a u : SU σ n) :
    (mat σ n (a * u * a⁻¹) - 1).rank = (mat σ n u - 1).rank := by
  have h : mat σ n (a * u * a⁻¹) - 1 = mat σ n a * (mat σ n u - 1) * mat σ n a⁻¹ := by
    rw [map_mul, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      ← map_mul (mat σ n) a a⁻¹, mul_inv_cancel, map_one]
  have hdet : ∀ b : SU σ n, IsUnit (mat σ n b).det := fun b => by
    have h1 : (mat σ n b).det = 1 := b.2.1
    rw [h1]
    exact isUnit_one
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hdet _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hdet _)]

theorem rank_mat_ggInvSU_sub_one {l : ℕ} (h : 2 * l ≤ n) :
    (mat σ n (ggInvSU σ n l) - 1).rank = l := by
  rw [mat_apply, coe_ggInvSU σ h, ggInvUMatrix, add_sub_cancel_left]
  exact rank_ggInvUNil h

private def corner0 (m : ℕ) : Fin (m + 4) := ⟨0, by omega⟩
private def corner1 (m : ℕ) : Fin (m + 4) := ⟨1, by omega⟩
private def corner2 (m : ℕ) : Fin (m + 4) := ⟨m + 2, by omega⟩
private def corner3 (m : ℕ) : Fin (m + 4) := ⟨m + 3, by omega⟩

private lemma corner_pairwise (m : ℕ) :
    corner0 m ≠ corner1 m ∧ corner0 m ≠ corner2 m ∧ corner0 m ≠ corner3 m ∧
      corner1 m ≠ corner2 m ∧ corner1 m ≠ corner3 m ∧ corner2 m ≠ corner3 m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have hv := congrArg Fin.val h <;>
    simp only [corner0, corner1, corner2, corner3] at hv <;> omega

private lemma rev_corner0 (m : ℕ) : Fin.rev (corner0 m) = corner3 m := by
  ext
  simp [corner0, corner3]

private lemma rev_corner1 (m : ℕ) : Fin.rev (corner1 m) = corner2 m := by
  ext
  simp [corner1, corner2, Fin.val_rev]

omit [CharP F 2] in
private lemma ggInvUNil_two_apply_corner0 (m : ℕ) (a : Fin (m + 4)) :
    ggInvUNil (m + 4) 2 F a (corner0 m) = if a = corner3 m then 1 else 0 := by
  rw [ggInvUNil_apply]
  by_cases ha : (a : ℕ) = m + 3
  · have ha' : a = corner3 m := by ext; simpa [corner3] using ha
    subst ha'
    simp [corner0, corner3]
  · have hc : ¬ ((corner0 m : ℕ) < 2 ∧ (a : ℕ) + (corner0 m : ℕ) + 1 = m + 4 ∧
        (corner0 m : ℕ) < a) := by
      intro hh
      apply ha
      have h0 : (corner0 m : ℕ) = 0 := rfl
      omega
    rw [if_neg hc]
    simp [ha, corner3, Fin.ext_iff]

omit [CharP F 2] in
private lemma ggInvUNil_two_apply_corner1 (m : ℕ) (a : Fin (m + 4)) :
    ggInvUNil (m + 4) 2 F a (corner1 m) = if a = corner2 m then 1 else 0 := by
  rw [ggInvUNil_apply]
  by_cases ha : (a : ℕ) = m + 2
  · have ha' : a = corner2 m := by ext; simpa [corner2] using ha
    subst ha'
    simp [corner1, corner2]
  · have hc : ¬ ((corner1 m : ℕ) < 2 ∧ (a : ℕ) + (corner1 m : ℕ) + 1 = m + 4 ∧
        (corner1 m : ℕ) < a) := by
      intro hh
      apply ha
      have h1 : (corner1 m : ℕ) = 1 := rfl
      omega
    rw [if_neg hc]
    simp [ha, corner2, Fin.ext_iff]

omit [CharP F 2] in
private lemma ggInvUNil_two_apply_other (m : ℕ) (a : Fin (m + 4)) {b : Fin (m + 4)}
    (hb0 : (b : ℕ) ≠ 0) (hb1 : (b : ℕ) ≠ 1) :
    ggInvUNil (m + 4) 2 F a b = 0 := by
  rw [ggInvUNil_apply, if_neg]
  intro hh
  omega

omit [CharP F 2] in
private lemma ggInvUNil_two_apply (m : ℕ) (a b : Fin (m + 4)) :
    ggInvUNil (m + 4) 2 F a b =
      (if a = corner3 m ∧ b = corner0 m then 1 else 0) +
        (if a = corner2 m ∧ b = corner1 m then 1 else 0) := by
  by_cases hb0 : (b : ℕ) = 0
  · have hb : b = corner0 m := by ext; simpa [corner0] using hb0
    subst hb
    rw [ggInvUNil_two_apply_corner0]
    simp [(corner_pairwise m).1]
  · by_cases hb1 : (b : ℕ) = 1
    · have hb : b = corner1 m := by ext; simpa [corner1] using hb1
      subst hb
      rw [ggInvUNil_two_apply_corner1]
      simp [(corner_pairwise m).1.symm]
    · rw [ggInvUNil_two_apply_other m a hb0 hb1]
      have hbc0 : b ≠ corner0 m := fun h => hb0 (by rw [h]; rfl)
      have hbc1 : b ≠ corner1 m := fun h => hb1 (by rw [h]; rfl)
      simp [hbc0, hbc1]

omit [CharP F 2] in
private lemma ggInvUNil_two (m : ℕ) :
    ggInvUNil (m + 4) 2 F =
      single (corner3 m) (corner0 m) 1 + single (corner2 m) (corner1 m) 1 := by
  ext a b
  rw [ggInvUNil_two_apply]
  simp only [Matrix.add_apply, Matrix.single_apply]
  by_cases h1 : a = corner3 m ∧ b = corner0 m
  · rcases h1 with ⟨rfl, rfl⟩
    simp [corner0, corner1, corner2, corner3]
  · by_cases h2 : a = corner2 m ∧ b = corner1 m
    · rcases h2 with ⟨rfl, rfl⟩
      simp [corner0, corner1, corner2, corner3]
    · simp [h1, h2, eq_comm]

omit [CharP F 2] in
private lemma ggInvUNil_one_apply (m : ℕ) (a b : Fin (m + 4)) :
    ggInvUNil (m + 4) 1 F a b = if a = corner3 m ∧ b = corner0 m then 1 else 0 := by
  rw [ggInvUNil_apply]
  by_cases hb : (b : ℕ) = 0
  · have hb' : b = corner0 m := by ext; simpa [corner0] using hb
    subst hb'
    by_cases ha : (a : ℕ) = m + 3
    · have ha' : a = corner3 m := by ext; simpa [corner3] using ha
      subst ha'
      simp [corner0, corner3]
    · have hc : ¬ ((corner0 m : ℕ) < 1 ∧ (a : ℕ) + (corner0 m : ℕ) + 1 = m + 4 ∧
          (corner0 m : ℕ) < a) := by
        intro hh
        apply ha
        have h0 : (corner0 m : ℕ) = 0 := rfl
        omega
      have h1 : ¬ (a = corner3 m) := fun h => ha (by rw [h]; rfl)
      rw [if_neg hc]
      simp [ha, corner0, corner3, Fin.ext_iff]
  · have hc : ¬ ((b : ℕ) < 1 ∧ (a : ℕ) + b + 1 = m + 4 ∧ (b : ℕ) < a) := by
      intro hh
      omega
    have h1 : ¬ (a = corner3 m ∧ b = corner0 m) := by
      intro hh
      exact hb (by rw [hh.2]; rfl)
    rw [if_neg hc]
    simp [h1]

omit [CharP F 2] in
private lemma ggInvUNil_one (m : ℕ) :
    ggInvUNil (m + 4) 1 F = single (corner3 m) (corner0 m) 1 := by
  ext a b
  rw [ggInvUNil_one_apply, Matrix.single_apply]
  by_cases h : a = corner3 m ∧ b = corner0 m
  · rcases h with ⟨rfl, rfl⟩
    simp [corner0, corner3]
  · simp [h, eq_comm]

omit [CharP F 2] in
private lemma ggInvUNil_apply_rev {l : ℕ} (h : 2 * l ≤ n) {a x : Fin n}
    (ha : (a : ℕ) < l) :
    ggInvUNil n l F x a = if x = Fin.rev a then 1 else 0 := by
  rw [ggInvUNil_apply]
  by_cases hx : x = Fin.rev a
  · subst hx
    rw [if_pos ⟨ha, by simp only [Fin.val_rev]; omega,
      by simp only [Fin.val_rev]; omega⟩, if_pos rfl]
  · have hneg : ¬ ((a : ℕ) < l ∧ (x : ℕ) + a + 1 = n ∧ (a : ℕ) < x) := by
      intro hc
      exact hx (Fin.ext (by
        have := hc.2.1
        simp only [Fin.val_rev]
        omega))
    rw [if_neg hneg, if_neg hx]

omit [CharP F 2] in
private lemma ggInvUNil_apply_rev_row {l : ℕ} (h : 2 * l ≤ n) {b y : Fin n}
    (hb : ((Fin.rev b : Fin n) : ℕ) < l) :
    ggInvUNil n l F b y = if y = Fin.rev b then 1 else 0 := by
  rw [ggInvUNil_apply]
  by_cases hy : y = Fin.rev b
  · subst hy
    have hsum : (b : ℕ) + (Fin.rev b : Fin n) + 1 = n := by
      simp only [Fin.val_rev]
      omega
    have hlt : ((Fin.rev b : Fin n) : ℕ) < b := by
      simp only [Fin.val_rev] at hb ⊢
      omega
    rw [if_pos ⟨hb, hsum, hlt⟩, if_pos rfl]
  · have hneg : ¬ ((y : ℕ) < l ∧ (b : ℕ) + y + 1 = n ∧ (y : ℕ) < b) := by
      intro hc
      exact hy (Fin.ext (by
        have := hc.2.1
        simp only [Fin.val_rev]
        omega))
    rw [if_neg hneg, if_neg hy]

omit [CharP F 2] in
private lemma ggInvUNil_mul_single {l : ℕ} (h : 2 * l ≤ n) (a b : Fin n) (c : F) :
    ggInvUNil n l F * single a b c =
      if (a : ℕ) < l then single (Fin.rev a) b c else 0 := by
  ext x y
  by_cases hy : y = b
  · subst hy
    rw [Matrix.mul_single_apply_same]
    by_cases ha : (a : ℕ) < l
    · rw [if_pos ha]
      by_cases hx : x = Fin.rev a
      · subst hx
        rw [ggInvUNil_apply_rev h ha, if_pos rfl, Matrix.single_apply_same, one_mul]
      · rw [ggInvUNil_apply_rev h ha, if_neg hx, zero_mul, Matrix.single_apply,
          if_neg (fun hh => hx hh.1.symm)]
    · rw [if_neg ha, Matrix.zero_apply]
      have hneg : ¬ ((a : ℕ) < l ∧ (x : ℕ) + a + 1 = n ∧ (a : ℕ) < x) :=
        fun hh => ha hh.1
      rw [ggInvUNil_apply, if_neg hneg, zero_mul]
  · rw [Matrix.mul_single_apply_of_ne c a b x y hy]
    by_cases ha : (a : ℕ) < l
    · rw [if_pos ha, Matrix.single_apply, if_neg (fun hh => hy hh.2.symm)]
    · rw [if_neg ha, Matrix.zero_apply]

omit [CharP F 2] in
private lemma single_mul_ggInvUNil {l : ℕ} (h : 2 * l ≤ n) (a b : Fin n) (c : F) :
    single a b c * ggInvUNil n l F =
      if ((Fin.rev b : Fin n) : ℕ) < l then single a (Fin.rev b) c else 0 := by
  ext x y
  by_cases hx : x = a
  · subst hx
    rw [Matrix.single_mul_apply_same]
    by_cases hb : ((Fin.rev b : Fin n) : ℕ) < l
    · rw [if_pos hb]
      by_cases hy : y = Fin.rev b
      · subst hy
        rw [ggInvUNil_apply_rev_row h hb, if_pos rfl, Matrix.single_apply_same, mul_one]
      · rw [ggInvUNil_apply_rev_row h hb, if_neg hy, mul_zero, Matrix.single_apply,
          if_neg (fun hh => hy hh.2.symm)]
    · rw [if_neg hb, Matrix.zero_apply]
      have hneg : ¬ ((y : ℕ) < l ∧ (b : ℕ) + y + 1 = n ∧ (y : ℕ) < b) := by
        intro hc
        exact hb (by
          have := hc.2.1
          simp only [Fin.val_rev]
          omega)
      rw [ggInvUNil_apply, if_neg hneg, mul_zero]
  · rw [Matrix.single_mul_apply_of_ne c a b x y hx (ggInvUNil n l F)]
    by_cases hb : ((Fin.rev b : Fin n) : ℕ) < l
    · rw [if_pos hb, Matrix.single_apply, if_neg (fun hh => hx hh.1.symm)]
    · rw [if_neg hb, Matrix.zero_apply]

private lemma rev_corner2 (m : ℕ) : Fin.rev (corner2 m) = corner1 m := by
  rw [← rev_corner1 m, Fin.rev_rev]

private lemma rev_corner3 (m : ℕ) : Fin.rev (corner3 m) = corner0 m := by
  rw [← rev_corner0 m, Fin.rev_rev]

private def nilSplit (m l : ℕ) (F : Type) [Field F] :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  ggInvUNil (m + 4) l F - ggInvUNil (m + 4) 2 F

omit [CharP F 2] in
private lemma ggInvUNil_eq_nilSplit_add_two (m l : ℕ) :
    ggInvUNil (m + 4) l F = nilSplit m l F + ggInvUNil (m + 4) 2 F := by
  rw [nilSplit]
  abel

omit [CharP F 2] in
private lemma ggInvUNil_mul_ggInvUNil_two (m : ℕ) {l : ℕ} (_hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    ggInvUNil (m + 4) l F * ggInvUNil (m + 4) 2 F = 0 := by
  rw [ggInvUNil_two, Matrix.mul_add, ggInvUNil_mul_single h2l,
    ggInvUNil_mul_single h2l]
  have h3 : ¬ ((corner3 m : ℕ) < l) := by simp [corner3] ; omega
  have h2 : ¬ ((corner2 m : ℕ) < l) := by simp [corner2] ; omega
  rw [if_neg h3, if_neg h2, add_zero]

omit [CharP F 2] in
private lemma ggInvUNil_two_mul_ggInvUNil (m : ℕ) {l : ℕ} (_hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    ggInvUNil (m + 4) 2 F * ggInvUNil (m + 4) l F = 0 := by
  rw [ggInvUNil_two, Matrix.add_mul, single_mul_ggInvUNil h2l,
    single_mul_ggInvUNil h2l]
  have h3 : ¬ (((Fin.rev (corner0 m) : Fin (m + 4)) : ℕ) < l) := by
    rw [rev_corner0]; simp [corner3]; omega
  have h2 : ¬ (((Fin.rev (corner1 m) : Fin (m + 4)) : ℕ) < l) := by
    rw [rev_corner1]; simp [corner2]; omega
  rw [if_neg h3, if_neg h2, add_zero]

omit [CharP F 2] in
private lemma nilSplit_mul_self (m : ℕ) {l : ℕ} (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    nilSplit m l F * nilSplit m l F = 0 := by
  rw [nilSplit, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    ggInvUNil_mul_self, ggInvUNil_mul_ggInvUNil_two m hl h2l,
    ggInvUNil_two_mul_ggInvUNil m hl h2l, ggInvUNil_mul_self]
  abel

omit [CharP F 2] in
private lemma nilSplit_mul_single_corner (m : ℕ) {l : ℕ} (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4)
    {a : Fin (m + 4)} (ha : a = corner0 m ∨ a = corner1 m ∨ a = corner2 m ∨ a = corner3 m)
    (b : Fin (m + 4)) (c : F) : nilSplit m l F * single a b c = 0 := by
  rcases ha with rfl | rfl | rfl | rfl
  · rw [nilSplit, Matrix.sub_mul, ggInvUNil_mul_single h2l,
      ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h0l : (corner0 m : ℕ) < l := by simp [corner0] ; omega
    have h02 : (corner0 m : ℕ) < 2 := by simp [corner0]
    rw [if_pos h0l, if_pos h02, sub_self]
  · rw [nilSplit, Matrix.sub_mul, ggInvUNil_mul_single h2l,
      ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h1l : (corner1 m : ℕ) < l := by simp [corner1] ; omega
    have h12 : (corner1 m : ℕ) < 2 := by simp [corner1]
    rw [if_pos h1l, if_pos h12, sub_self]
  · rw [nilSplit, Matrix.sub_mul, ggInvUNil_mul_single h2l,
      ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h2l' : ¬ ((corner2 m : ℕ) < l) := by simp [corner2] ; omega
    have h22 : ¬ ((corner2 m : ℕ) < 2) := by simp [corner2]
    rw [if_neg h2l', if_neg h22, sub_zero]
  · rw [nilSplit, Matrix.sub_mul, ggInvUNil_mul_single h2l,
      ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h3l : ¬ ((corner3 m : ℕ) < l) := by simp [corner3] ; omega
    have h32 : ¬ ((corner3 m : ℕ) < 2) := by simp [corner3]
    rw [if_neg h3l, if_neg h32, sub_zero]

omit [CharP F 2] in
private lemma single_mul_nilSplit_corner (m : ℕ) {l : ℕ} (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4)
    (b : Fin (m + 4)) {a : Fin (m + 4)}
    (ha : a = corner0 m ∨ a = corner1 m ∨ a = corner2 m ∨ a = corner3 m)
    (c : F) : single b a c * nilSplit m l F = 0 := by
  rcases ha with rfl | rfl | rfl | rfl
  · rw [nilSplit, Matrix.mul_sub, single_mul_ggInvUNil h2l,
      single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h3l : ¬ (((Fin.rev (corner0 m) : Fin (m + 4)) : ℕ) < l) := by
      rw [rev_corner0]; simp [corner3]; omega
    have h32 : ¬ (((Fin.rev (corner0 m) : Fin (m + 4)) : ℕ) < 2) := by
      rw [rev_corner0]; simp [corner3]
    rw [if_neg h3l, if_neg h32, sub_zero]
  · rw [nilSplit, Matrix.mul_sub, single_mul_ggInvUNil h2l,
      single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h2l' : ¬ (((Fin.rev (corner1 m) : Fin (m + 4)) : ℕ) < l) := by
      rw [rev_corner1]; simp [corner2]; omega
    have h22 : ¬ (((Fin.rev (corner1 m) : Fin (m + 4)) : ℕ) < 2) := by
      rw [rev_corner1]; simp [corner2]
    rw [if_neg h2l', if_neg h22, sub_zero]
  · rw [nilSplit, Matrix.mul_sub, single_mul_ggInvUNil h2l,
      single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h1l : (((Fin.rev (corner2 m) : Fin (m + 4)) : ℕ) < l) := by
      rw [rev_corner2]; simp [corner1]; omega
    have h12 : (((Fin.rev (corner2 m) : Fin (m + 4)) : ℕ) < 2) := by
      rw [rev_corner2]; simp [corner1]
    rw [if_pos h1l, if_pos h12, sub_self]
  · rw [nilSplit, Matrix.mul_sub, single_mul_ggInvUNil h2l,
      single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
    have h0l : (((Fin.rev (corner3 m) : Fin (m + 4)) : ℕ) < l) := by
      rw [rev_corner3]; simp [corner0]; omega
    have h02 : (((Fin.rev (corner3 m) : Fin (m + 4)) : ℕ) < 2) := by
      rw [rev_corner3]; simp [corner0]
    rw [if_pos h0l, if_pos h02, sub_self]

omit [CharP F 2] in
private lemma nilSplit_apply_eq_zero_of_corner_col (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) (a : Fin (m + 4)) {b : Fin (m + 4)}
    (hb : b = corner0 m ∨ b = corner1 m ∨ b = corner2 m ∨ b = corner3 m) :
    nilSplit m l F a b = 0 := by
  have h := congrFun (congrFun (nilSplit_mul_single_corner (F := F) m hl h2l hb b 1) a) b
  simpa only [Matrix.mul_single_apply_same, mul_one, Matrix.zero_apply] using h

omit [CharP F 2] in
private lemma nilSplit_apply_eq_zero_of_corner_row (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) {a : Fin (m + 4)}
    (ha : a = corner0 m ∨ a = corner1 m ∨ a = corner2 m ∨ a = corner3 m)
    (b : Fin (m + 4)) : nilSplit m l F a b = 0 := by
  have h := congrFun (congrFun (single_mul_nilSplit_corner (F := F) m hl h2l a ha 1) a) b
  simpa only [Matrix.single_mul_apply_same, one_mul, Matrix.zero_apply] using h

private def cornerE (m : ℕ) (F : Type) [Field F] (a b : Fin (m + 4)) :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F := single a b 1

private def cornerG (m : ℕ) (F : Type) [Field F] :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  1 + cornerE m F (corner0 m) (corner1 m) + cornerE m F (corner2 m) (corner3 m)

private def cornerLam (m : ℕ) (F : Type) [Field F] :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  1 + cornerE m F (corner1 m) (corner2 m)

private def cornerX (m : ℕ) (F : Type) [Field F] :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  cornerE m F (corner3 m) (corner0 m) + cornerE m F (corner2 m) (corner0 m) +
    cornerE m F (corner3 m) (corner1 m)

private def cornerY (m : ℕ) (F : Type) [Field F] (lam mu : F) :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  single (corner3 m) (corner0 m) (mu * lam) +
    single (corner2 m) (corner0 m) (lam * lam) +
      single (corner3 m) (corner1 m) (mu * mu) +
        single (corner1 m) (corner0 m) (lam / mu) +
          single (corner3 m) (corner2 m) (mu / lam)

private lemma cornerX_mul_cornerX (m : ℕ) (F : Type) [Field F] :
    cornerX m F * cornerX m F = 0 := by
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h12 : corner1 m ≠ corner2 m := (corner_pairwise m).2.2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  simp [cornerX, cornerE, Matrix.add_mul, Matrix.mul_add, h02, h03, h12, h13,
    Matrix.single_mul_single_of_ne]

private lemma cornerX_mul_cornerY (m : ℕ) (F : Type) [Field F] (lam mu : F) :
    cornerX m F * cornerY m F lam mu = single (corner3 m) (corner0 m) (lam / mu) := by
  have h01 : corner0 m ≠ corner1 m := (corner_pairwise m).1
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h12 : corner1 m ≠ corner2 m := (corner_pairwise m).2.2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  simp [cornerX, cornerY, cornerE, Matrix.add_mul, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h01, h02, h03, h12, h13,
    add_zero, zero_add, one_mul]

private lemma cornerY_mul_cornerX (m : ℕ) (F : Type) [Field F] (lam mu : F) :
    cornerY m F lam mu * cornerX m F = single (corner3 m) (corner0 m) (mu / lam) := by
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h12 : corner1 m ≠ corner2 m := (corner_pairwise m).2.2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  have h23 : corner2 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.2
  simp [cornerX, cornerY, cornerE, Matrix.add_mul, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h02, h03, h12, h13, h23,
    add_zero, zero_add, mul_one]

private lemma cornerY_mul_cornerY (m : ℕ) (F : Type) [Field F] [CharP F 2] {lam mu : F}
    (_hlam0 : lam ≠ 0) (_hmu0 : mu ≠ 0) :
    cornerY m F lam mu * cornerY m F lam mu = 0 := by
  have h01 : corner0 m ≠ corner1 m := (corner_pairwise m).1
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h12 : corner1 m ≠ corner2 m := (corner_pairwise m).2.2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  have h21 : corner2 m ≠ corner1 m := (corner_pairwise m).2.2.2.1.symm
  have h23 : corner2 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.2
  simp [cornerY, Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h01, h02, h03, h12, h13, h21, h23,
    add_zero, zero_add]
  have hcoef : mu * mu * (lam / mu) + mu / lam * (lam * lam) = 0 := by
    field_simp [_hlam0, _hmu0]
    rw [CharTwo.add_self_eq_zero, mul_zero]
  have hcoef' : mu / lam * (lam * lam) + mu * mu * (lam / mu) = 0 := by
    rw [add_comm]
    exact hcoef
  rw [← Matrix.single_add, hcoef', Matrix.single_zero]

private lemma cornerX_mul_cornerE30 (m : ℕ) (F : Type) [Field F] (c : F) :
    cornerX m F * single (corner3 m) (corner0 m) c = 0 := by
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  simp [cornerX, cornerE, Matrix.add_mul, Matrix.single_mul_single_of_ne, h03, h13,
    add_zero]

private lemma cornerE30_mul_cornerX (m : ℕ) (F : Type) [Field F] (c : F) :
    single (corner3 m) (corner0 m) c * cornerX m F = 0 := by
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  simp [cornerX, cornerE, Matrix.mul_add, Matrix.single_mul_single_of_ne, h02, h03,
    add_zero]

private lemma cornerE30_mul_cornerY (m : ℕ) (F : Type) [Field F] (c : F) (lam mu : F) :
    single (corner3 m) (corner0 m) c * cornerY m F lam mu = 0 := by
  have h01 : corner0 m ≠ corner1 m := (corner_pairwise m).1
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  simp [cornerY, Matrix.mul_add, Matrix.single_mul_single_of_ne, h01, h02, h03,
    add_zero]

private lemma cornerY_mul_cornerE30 (m : ℕ) (F : Type) [Field F] (c : F) (lam mu : F) :
    cornerY m F lam mu * single (corner3 m) (corner0 m) c = 0 := by
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  have h13 : corner1 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.1
  have h23 : corner2 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.2
  simp [cornerY, Matrix.add_mul, Matrix.single_mul_single_of_ne, h03, h13, h23,
    add_zero]

private lemma cornerE30_mul_cornerE30 (m : ℕ) (F : Type) [Field F] (c d : F) :
    single (corner3 m) (corner0 m) c * single (corner3 m) (corner0 m) d = 0 := by
  have h03 : corner0 m ≠ corner3 m := (corner_pairwise m).2.2.1
  simp [Matrix.single_mul_single_of_ne, h03]

private lemma one_mem_traceZero : (1 : F) ∈ traceZero σ := by
  rw [mem_traceZero, map_one, CharTwo.add_self_eq_zero]

private lemma mat_rootHom_cornerG (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    mat σ (m + 4)
      (rootHom σ hσ.invol (i := corner0 m) (j := corner1 m)
        (hij := (corner_pairwise m).1)
        (hi := by rw [rev_corner0]; exact (corner_pairwise m).2.2.1)
        (hj := by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1)
        (Multiplicative.ofAdd 1)) = cornerG m F := by
  rw [mat_apply, coe_rootHom, rootMatrix]
  rw [toAdd_ofAdd, map_one, rev_corner1, rev_corner0]
  rw [cornerG, cornerE]
  have hneg : -(single (corner2 m) (corner3 m) (1 : F)) =
      single (corner2 m) (corner3 m) 1 := by
    simp [CharTwo.neg_eq]
  rw [sub_eq_add_neg, hneg]
  simp only [cornerE]

private lemma mat_longRootHom_cornerLam (_hσ : IsUnitaryInvolution σ) (m : ℕ) :
    mat σ (m + 4)
      (longRootHom σ (i := corner1 m)
        (by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1)
        (Multiplicative.ofAdd (⟨1, one_mem_traceZero (σ := σ)⟩ : traceZero σ))) =
      cornerLam m F := by
  rw [mat_apply, coe_longRootHom, longRootMatrix, cornerLam, cornerE, rev_corner1]
  simp

private lemma cornerG_mul_ggInvUNil_two (m : ℕ) (F : Type) [Field F] [CharP F 2] :
    cornerG m F * ggInvUNil (m + 4) 2 F =
      ggInvUNil (m + 4) 2 F + single (corner2 m) (corner0 m) 1 := by
  rw [cornerG, cornerE, cornerE, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul,
    single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4),
    single_mul_ggInvUNil (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
  have h1 : ¬ (((Fin.rev (corner1 m) : Fin (m + 4)) : ℕ) < 2) := by
    rw [rev_corner1]; simp [corner2]
  have h3 : (((Fin.rev (corner3 m) : Fin (m + 4)) : ℕ) < 2) := by
    rw [rev_corner3]; simp [corner0]
  rw [if_neg h1, if_pos h3, rev_corner3, add_zero]

private lemma ggInvUNil_two_mul_cornerG (m : ℕ) (F : Type) [Field F] [CharP F 2] :
    ggInvUNil (m + 4) 2 F * cornerG m F =
      ggInvUNil (m + 4) 2 F + single (corner3 m) (corner1 m) 1 := by
  rw [cornerG, cornerE, cornerE, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one,
    ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4),
    ggInvUNil_mul_single (F := F) (n := m + 4) (l := 2) (by omega : 2 * 2 ≤ m + 4)]
  have h0 : (corner0 m : ℕ) < 2 := by simp [corner0]
  have h2 : ¬ ((corner2 m : ℕ) < 2) := by simp [corner2]
  rw [if_pos h0, rev_corner0, if_neg h2, add_zero]

private lemma cornerE20_mul_cornerG (m : ℕ) (F : Type) [Field F] :
    single (corner2 m) (corner0 m) 1 * cornerG m F =
      single (corner2 m) (corner0 m) 1 + single (corner2 m) (corner1 m) 1 := by
  have h02 : corner0 m ≠ corner2 m := (corner_pairwise m).2.1
  simp [cornerG, cornerE, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h02]

private lemma cornerG_mul_ggInvUNil_two_mul_cornerG (m : ℕ) (F : Type) [Field F] [CharP F 2] :
    cornerG m F * ggInvUNil (m + 4) 2 F * cornerG m F = cornerX m F := by
  have hN2 : ggInvUNil (m + 4) 2 F + single (corner2 m) (corner1 m) 1 =
      single (corner3 m) (corner0 m) 1 := by
    rw [ggInvUNil_two (F := F), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  calc cornerG m F * ggInvUNil (m + 4) 2 F * cornerG m F
      = (cornerG m F * ggInvUNil (m + 4) 2 F) * cornerG m F := by rw [Matrix.mul_assoc]
    _ = (ggInvUNil (m + 4) 2 F + single (corner2 m) (corner0 m) 1) * cornerG m F := by
      rw [cornerG_mul_ggInvUNil_two m F]
    _ = ggInvUNil (m + 4) 2 F * cornerG m F +
        single (corner2 m) (corner0 m) 1 * cornerG m F := by rw [Matrix.add_mul]
    _ = (ggInvUNil (m + 4) 2 F + single (corner3 m) (corner1 m) 1) +
        (single (corner2 m) (corner0 m) 1 + single (corner2 m) (corner1 m) 1) := by
      rw [ggInvUNil_two_mul_cornerG m F, cornerE20_mul_cornerG m F]
    _ = (ggInvUNil (m + 4) 2 F + single (corner2 m) (corner1 m) 1) +
        (single (corner3 m) (corner1 m) 1 + single (corner2 m) (corner0 m) 1) := by abel
    _ = single (corner3 m) (corner0 m) 1 +
        (single (corner3 m) (corner1 m) 1 + single (corner2 m) (corner0 m) 1) := by rw [hN2]
    _ = cornerX m F := by rw [cornerX, cornerE, cornerE, cornerE]; abel

omit [CharP F 2] in
private lemma cornerG_mul_nilSplit (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    cornerG m F * nilSplit m l F = nilSplit m l F := by
  have h01 : single (corner0 m) (corner1 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (b := corner0 m) (a := corner1 m)
      (Or.inr (Or.inl rfl)) 1
  have h23 : single (corner2 m) (corner3 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (b := corner2 m) (a := corner3 m)
      (Or.inr (Or.inr (Or.inr rfl))) 1
  rw [cornerG, cornerE, cornerE, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, h01, h23]
  abel

omit [CharP F 2] in
private lemma nilSplit_mul_cornerG (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    nilSplit m l F * cornerG m F = nilSplit m l F := by
  have h01 : nilSplit m l F * single (corner0 m) (corner1 m) 1 = 0 :=
    nilSplit_mul_single_corner (F := F) m hl h2l (Or.inl rfl) (corner1 m) 1
  have h23 : nilSplit m l F * single (corner2 m) (corner3 m) 1 = 0 :=
    nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inr (Or.inl rfl))) (corner3 m) 1
  rw [cornerG, cornerE, cornerE, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, h01, h23]
  abel

omit [CharP F 2] in
private lemma cornerLam_mul_nilSplit (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    cornerLam m F * nilSplit m l F = nilSplit m l F := by
  have h12 : single (corner1 m) (corner2 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (b := corner1 m) (a := corner2 m)
      (Or.inr (Or.inr (Or.inl rfl))) 1
  rw [cornerLam, cornerE, Matrix.add_mul, Matrix.one_mul, h12]
  abel

omit [CharP F 2] in
private lemma nilSplit_mul_cornerLam (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    nilSplit m l F * cornerLam m F = nilSplit m l F := by
  have h12 : nilSplit m l F * single (corner1 m) (corner2 m) 1 = 0 :=
    nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inl rfl)) (corner2 m) 1
  rw [cornerLam, cornerE, Matrix.mul_add, Matrix.mul_one, h12]
  abel

private lemma cornerLam_mul_cornerX (m : ℕ) (F : Type) [Field F] :
    cornerLam m F * cornerX m F = cornerX m F + single (corner1 m) (corner0 m) 1 := by
  have h23 : corner2 m ≠ corner3 m := (corner_pairwise m).2.2.2.2.2
  simp [cornerLam, cornerX, cornerE, Matrix.add_mul, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h23]
  abel

private lemma cornerX_mul_cornerLam (m : ℕ) (F : Type) [Field F] :
    cornerX m F * cornerLam m F = cornerX m F + single (corner3 m) (corner2 m) 1 := by
  have h01 : corner0 m ≠ corner1 m := (corner_pairwise m).1
  simp [cornerLam, cornerX, cornerE, Matrix.add_mul, Matrix.mul_add,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h01]

private lemma cornerE10_mul_cornerLam (m : ℕ) (F : Type) [Field F] :
    single (corner1 m) (corner0 m) 1 * cornerLam m F = single (corner1 m) (corner0 m) 1 := by
  have h01 : corner0 m ≠ corner1 m := (corner_pairwise m).1
  simp [cornerLam, cornerE, Matrix.mul_add,
    Matrix.single_mul_single_of_ne, h01]

private lemma cornerLam_mul_cornerX_mul_cornerLam (m : ℕ) (F : Type) [Field F] :
    cornerLam m F * cornerX m F * cornerLam m F =
      cornerX m F + single (corner1 m) (corner0 m) 1 + single (corner3 m) (corner2 m) 1 := by
  calc cornerLam m F * cornerX m F * cornerLam m F
      = (cornerLam m F * cornerX m F) * cornerLam m F := by rw [Matrix.mul_assoc]
    _ = (cornerX m F + single (corner1 m) (corner0 m) 1) * cornerLam m F := by
      rw [cornerLam_mul_cornerX m F]
    _ = cornerX m F * cornerLam m F + single (corner1 m) (corner0 m) 1 * cornerLam m F := by
      rw [Matrix.add_mul]
    _ = (cornerX m F + single (corner3 m) (corner2 m) 1) + single (corner1 m) (corner0 m) 1 := by
      rw [cornerX_mul_cornerLam m F, cornerE10_mul_cornerLam m F]
    _ = cornerX m F + single (corner1 m) (corner0 m) 1 + single (corner3 m) (corner2 m) 1 := by
      abel

private def diagT (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) (lam mu : F) :
    Fin (m + 4) → F :=
  fun k => RootDetectSU.pairDiag σ (corner0 m) lam⁻¹ k *
    RootDetectSU.pairDiag σ (corner1 m) mu⁻¹ k

private lemma diagT_corner0 (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) (lam mu : F) :
    diagT m F σ lam mu (corner0 m) = lam⁻¹ := by
  have h := corner_pairwise m
  rw [diagT]
  simp [RootDetectSU.pairDiag_self, RootDetectSU.pairDiag_of_ne, h.1, h.2.1, rev_corner1]

private lemma diagT_corner1 (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) (lam mu : F) :
    diagT m F σ lam mu (corner1 m) = mu⁻¹ := by
  have h := corner_pairwise m
  rw [diagT]
  simp [RootDetectSU.pairDiag_self, RootDetectSU.pairDiag_of_ne, h.2.2.2.2.1,
    h.1.symm, rev_corner0]

private lemma diagT_corner2 (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) {lam mu : F}
    (hσ : IsUnitaryInvolution σ) (hmu : mu = σ lam) :
    diagT m F σ lam mu (corner2 m) = lam := by
  have h := corner_pairwise m
  rw [diagT, hmu]
  rw [show corner2 m = Fin.rev (corner1 m) from (rev_corner1 m).symm]
  rw [RootDetectSU.pairDiag_of_ne (b := corner0 m) (a := Fin.rev (corner1 m))
    (by rw [rev_corner1]; exact h.2.1.symm)
    (by rw [rev_corner1]; exact h.2.2.2.2.2) lam⁻¹]
  rw [RootDetectSU.pairDiag_rev (b := corner1 m) h.2.2.2.1 (x := (σ lam)⁻¹), one_mul]
  simp [map_inv₀, inv_inv, hσ.invol]

private lemma diagT_corner3 (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) {lam mu : F}
    (_hσ : IsUnitaryInvolution σ) (hmu : mu = σ lam) :
    diagT m F σ lam mu (corner3 m) = mu := by
  have h := corner_pairwise m
  rw [diagT, hmu]
  rw [show corner3 m = Fin.rev (corner0 m) from (rev_corner0 m).symm]
  rw [RootDetectSU.pairDiag_rev (b := corner0 m) h.2.2.1 (x := lam⁻¹)]
  rw [RootDetectSU.pairDiag_of_ne (b := corner1 m) (a := Fin.rev (corner0 m))
    (by rw [rev_corner0]; exact h.2.2.2.2.1.symm)
    (by rw [rev_corner0]; exact h.2.2.2.2.2.symm) ((σ lam)⁻¹), mul_one]
  simp [map_inv₀, inv_inv]

private lemma diagT_apply_of_not_corner (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F) (lam mu : F)
    {k : Fin (m + 4)} (hk : ¬ (k = corner0 m ∨ k = corner1 m ∨ k = corner2 m ∨ k = corner3 m)) :
    diagT m F σ lam mu k = 1 := by
  have h0 : k ≠ corner0 m := fun h => hk (Or.inl h)
  have h1 : k ≠ corner1 m := fun h => hk (Or.inr (Or.inl h))
  have h2 : k ≠ corner2 m := fun h => hk (Or.inr (Or.inr (Or.inl h)))
  have h3 : k ≠ corner3 m := fun h => hk (Or.inr (Or.inr (Or.inr h)))
  simp [diagT, RootDetectSU.pairDiag_of_ne, h0, h1, h2, h3, rev_corner0, rev_corner1]

private lemma diagT_unitary (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F)
    (hσ : IsUnitaryInvolution σ) {lam mu : F} (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    ∀ a, σ (diagT m F σ lam mu a) * diagT m F σ lam mu (Fin.rev a) = 1 := by
  intro a
  exact RootDetectSU.unitary_mul
    (RootDetectSU.pairDiag_unitary hσ.invol (b := corner0 m)
      (by rw [rev_corner0]; exact (corner_pairwise m).2.2.1) (x := lam⁻¹) (inv_ne_zero hlam0))
    (RootDetectSU.pairDiag_unitary hσ.invol (b := corner1 m)
      (by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1) (x := mu⁻¹) (inv_ne_zero hmu0)) a

private lemma diagT_prod (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F)
    (hσ : IsUnitaryInvolution σ) {lam mu : F} (hmu : mu = σ lam)
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    ∏ k, diagT m F σ lam mu k = 1 := by
  change (∏ k, RootDetectSU.pairDiag σ (corner0 m) lam⁻¹ k *
      RootDetectSU.pairDiag σ (corner1 m) mu⁻¹ k) = 1
  rw [Finset.prod_mul_distrib,
    RootDetectSU.prod_pairDiag (b := corner0 m)
      (by rw [rev_corner0]; exact (corner_pairwise m).2.2.1),
    RootDetectSU.prod_pairDiag (b := corner1 m)
      (by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1)]
  have h1 : (σ (lam⁻¹))⁻¹ = mu := by rw [map_inv₀, inv_inv, hmu]
  have h2 : (σ (mu⁻¹))⁻¹ = lam := by rw [map_inv₀, inv_inv, hmu, hσ.invol]
  rw [h1, h2]
  calc (lam⁻¹ * mu) * (mu⁻¹ * lam) = (lam⁻¹ * lam) * (mu * mu⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hlam0, mul_inv_cancel₀ hmu0, one_mul]

private lemma diagonal_mul_single_mul_diagonal_inv (m : ℕ) (F : Type) [Field F]
    (t : Fin (m + 4) → F) (a b : Fin (m + 4)) (c : F) :
    diagonal t * single a b c * diagonal (fun k => (t k)⁻¹) =
      single a b (t a * c * (t b)⁻¹) := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : x = a ∧ y = b
  · rcases h with ⟨rfl, rfl⟩
    simp
  · have h' : ¬ (a = x ∧ b = y) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    rw [Matrix.single_apply, Matrix.single_apply, if_neg h', if_neg h']
    simp

private lemma diagonal_mul_cornerX_mul_diagonal_inv (m : ℕ) (F : Type) [Field F]
    (σ : F ≃+* F) {lam mu : F} (hσ : IsUnitaryInvolution σ) (hmu : mu = σ lam) :
    diagonal (diagT m F σ lam mu) * cornerX m F *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) =
      single (corner3 m) (corner0 m) (mu * lam) +
        single (corner2 m) (corner0 m) (lam * lam) +
          single (corner3 m) (corner1 m) (mu * mu) := by
  rw [cornerX, cornerE, cornerE, cornerE, Matrix.mul_add, Matrix.mul_add,
    Matrix.add_mul, Matrix.add_mul,
    diagonal_mul_single_mul_diagonal_inv, diagonal_mul_single_mul_diagonal_inv,
    diagonal_mul_single_mul_diagonal_inv,
    diagT_corner0 m F σ lam mu, diagT_corner1 m F σ lam mu,
    diagT_corner2 m F σ hσ hmu, diagT_corner3 m F σ hσ hmu]
  simp [inv_inv]

private lemma diagonal_mul_cornerE10_mul_diagonal_inv (m : ℕ) (F : Type) [Field F]
    (σ : F ≃+* F) {lam mu : F} (_hσ : IsUnitaryInvolution σ) (_hmu : mu = σ lam) :
    diagonal (diagT m F σ lam mu) * single (corner1 m) (corner0 m) 1 *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) =
      single (corner1 m) (corner0 m) (lam / mu) := by
  rw [diagonal_mul_single_mul_diagonal_inv, diagT_corner1 m F σ lam mu,
    diagT_corner0 m F σ lam mu, inv_inv, div_eq_mul_inv]
  simp [mul_comm]

private lemma diagonal_mul_cornerE32_mul_diagonal_inv (m : ℕ) (F : Type) [Field F]
    (σ : F ≃+* F) {lam mu : F} (hσ : IsUnitaryInvolution σ) (hmu : mu = σ lam) :
    diagonal (diagT m F σ lam mu) * single (corner3 m) (corner2 m) 1 *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) =
      single (corner3 m) (corner2 m) (mu / lam) := by
  rw [diagonal_mul_single_mul_diagonal_inv, diagT_corner3 m F σ hσ hmu,
    diagT_corner2 m F σ hσ hmu, div_eq_mul_inv]
  simp []

omit [CharP F 2] in
private lemma diagonal_mul_nilSplit_mul_diagonal_inv (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) (t : Fin (m + 4) → F)
    (ht : ∀ k, ¬ (k = corner0 m ∨ k = corner1 m ∨ k = corner2 m ∨ k = corner3 m) → t k = 1) :
    diagonal t * nilSplit m l F * diagonal (fun k => (t k)⁻¹) = nilSplit m l F := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : nilSplit m l F a b = 0
  · simp [hab]
  · have ha : ¬ (a = corner0 m ∨ a = corner1 m ∨ a = corner2 m ∨ a = corner3 m) :=
      fun h => hab (nilSplit_apply_eq_zero_of_corner_row m l hl h2l h b)
    have hb : ¬ (b = corner0 m ∨ b = corner1 m ∨ b = corner2 m ∨ b = corner3 m) :=
      fun h => hab (nilSplit_apply_eq_zero_of_corner_col m l hl h2l a h)
    rw [ht a ha, ht b hb]
    simp

private lemma mat_diagSU (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F)
    (t : Fin (m + 4) → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) :
    mat σ (m + 4) (RootDetectSU.diagSU σ t ht hdet) = diagonal t := by
  rw [mat_apply, RootDetectSU.coe_diagSU, RootDetectSU.coe_diagGL]

private lemma mat_diagSU_inv (m : ℕ) (F : Type) [Field F] (σ : F ≃+* F)
    (t : Fin (m + 4) → F) (ht : ∀ a, σ (t a) * t (Fin.rev a) = 1)
    (hdet : ∏ a, t a = 1) :
    mat σ (m + 4) ((RootDetectSU.diagSU σ t ht hdet)⁻¹) =
      diagonal (fun k => (t k)⁻¹) := by
  have ht0 : ∀ a, t a ≠ 0 := ne_zero_of_unitary ht
  have hdiag : diagonal t * diagonal (fun k => (t k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (ht0 k)
  have hd : (((RootDetectSU.diagSU σ t ht hdet : SU σ (m + 4)) : GL (Fin (m + 4)) F) :
      Matrix (Fin (m + 4)) (Fin (m + 4)) F) = diagonal t := by
    rw [← mat_apply, mat_diagSU m F σ t ht hdet]
  rw [mat_apply, Subgroup.coe_inv, Matrix.coe_units_inv, hd,
    Matrix.inv_eq_right_inv hdiag]

private noncomputable def cornerG1 (hσ : IsUnitaryInvolution σ) (m : ℕ) : SU σ (m + 4) :=
  rootHom σ hσ.invol (i := corner0 m) (j := corner1 m)
    (hij := (corner_pairwise m).1)
    (hi := by rw [rev_corner0]; exact (corner_pairwise m).2.2.1)
    (hj := by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1)
    (Multiplicative.ofAdd 1)

private noncomputable def cornerL (_hσ : IsUnitaryInvolution σ) (m : ℕ) : SU σ (m + 4) :=
  longRootHom σ (i := corner1 m)
    (by rw [rev_corner1]; exact (corner_pairwise m).2.2.2.1)
    (Multiplicative.ofAdd (⟨1, one_mem_traceZero (σ := σ)⟩ : traceZero σ))

private lemma mat_cornerG1 (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    mat σ (m + 4) (cornerG1 hσ m) = cornerG m F :=
  mat_rootHom_cornerG hσ m

private lemma mat_cornerL (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    mat σ (m + 4) (cornerL hσ m) = cornerLam m F :=
  mat_longRootHom_cornerLam hσ m

private lemma cornerG1_mul_self (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    cornerG1 hσ m * cornerG1 hσ m = 1 := by
  rw [cornerG1, ← map_mul,
    show Multiplicative.ofAdd (1 : F) * Multiplicative.ofAdd 1 = 1 by
      rw [← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero],
    map_one]

private lemma cornerL_mul_self (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    cornerL hσ m * cornerL hσ m = 1 := by
  have h1 : (⟨1, one_mem_traceZero (σ := σ)⟩ : traceZero σ) +
      ⟨1, one_mem_traceZero (σ := σ)⟩ = 0 := by
    ext
    simp [CharTwo.add_self_eq_zero]
  rw [cornerL, ← map_mul,
    show Multiplicative.ofAdd (⟨1, one_mem_traceZero (σ := σ)⟩ : traceZero σ) *
        Multiplicative.ofAdd ⟨1, one_mem_traceZero (σ := σ)⟩ = 1 by
      rw [← ofAdd_add, h1, ofAdd_zero],
    map_one]

private lemma mat_cornerG1_inv (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    mat σ (m + 4) ((cornerG1 hσ m)⁻¹) = cornerG m F := by
  rw [inv_eq_of_mul_eq_one_right (cornerG1_mul_self hσ m), mat_cornerG1]

private lemma cornerG_mul_self (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    cornerG m F * cornerG m F = 1 := by
  rw [← mat_cornerG1 hσ m, ← map_mul, cornerG1_mul_self, map_one]

private lemma cornerLam_mul_self (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    cornerLam m F * cornerLam m F = 1 := by
  rw [← mat_cornerL hσ m, ← map_mul, cornerL_mul_self, map_one]

private lemma mat_conj_cornerG1 (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) :
    mat σ (m + 4) (cornerG1 hσ m * ggInvSU σ (m + 4) l * (cornerG1 hσ m)⁻¹) =
      1 + nilSplit m l F + cornerX m F := by
  rw [map_mul, map_mul, mat_cornerG1_inv, mat_cornerG1, mat_apply, coe_ggInvSU σ h2l,
    ggInvUMatrix, ggInvUNil_eq_nilSplit_add_two (F := F)]
  calc cornerG m F * (1 + (nilSplit m l F + ggInvUNil (m + 4) 2 F)) * cornerG m F
      = (cornerG m F * 1 + cornerG m F * (nilSplit m l F + ggInvUNil (m + 4) 2 F)) *
          cornerG m F := by rw [Matrix.mul_add]
    _ = (cornerG m F + cornerG m F * (nilSplit m l F + ggInvUNil (m + 4) 2 F)) *
          cornerG m F := by rw [Matrix.mul_one]
    _ = cornerG m F * cornerG m F +
          cornerG m F * (nilSplit m l F + ggInvUNil (m + 4) 2 F) * cornerG m F := by
      rw [Matrix.add_mul, Matrix.mul_assoc]
    _ = 1 + cornerG m F * (nilSplit m l F + ggInvUNil (m + 4) 2 F) * cornerG m F := by
      rw [cornerG_mul_self hσ m]
    _ = 1 + (cornerG m F * nilSplit m l F * cornerG m F +
          cornerG m F * ggInvUNil (m + 4) 2 F * cornerG m F) := by
      rw [Matrix.mul_add, Matrix.add_mul]
    _ = 1 + (nilSplit m l F + cornerX m F) := by
      rw [cornerG_mul_nilSplit m l hl h2l, nilSplit_mul_cornerG m l hl h2l,
        cornerG_mul_ggInvUNil_two_mul_cornerG m F]
    _ = 1 + nilSplit m l F + cornerX m F := by abel

private noncomputable def cornerD (hσ : IsUnitaryInvolution σ) (m : ℕ) (lam mu : F)
    (hmu : mu = σ lam) (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) : SU σ (m + 4) :=
  RootDetectSU.diagSU σ (diagT m F σ lam mu)
    (diagT_unitary m F σ hσ hlam0 hmu0)
    (diagT_prod m F σ hσ hmu hlam0 hmu0)

private noncomputable def cornerX0 (hσ : IsUnitaryInvolution σ) (m l : ℕ) :
    SU σ (m + 4) :=
  cornerG1 hσ m * ggInvSU σ (m + 4) l * (cornerG1 hσ m)⁻¹

private noncomputable def cornerY0 (hσ : IsUnitaryInvolution σ) (m l : ℕ) (lam mu : F)
    (hmu : mu = σ lam) (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) : SU σ (m + 4) :=
  (cornerD hσ m lam mu hmu hlam0 hmu0 * cornerL hσ m) * cornerX0 hσ m l *
    (cornerD hσ m lam mu hmu hlam0 hmu0 * cornerL hσ m)⁻¹

omit [CharP F 2] in
private lemma mat_cornerD (hσ : IsUnitaryInvolution σ) (m : ℕ) {lam mu : F}
    (hmu : mu = σ lam) (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    mat σ (m + 4) (cornerD hσ m lam mu hmu hlam0 hmu0) = diagonal (diagT m F σ lam mu) := by
  rw [cornerD]
  exact mat_diagSU m F σ (diagT m F σ lam mu)
    (diagT_unitary m F σ hσ hlam0 hmu0) (diagT_prod m F σ hσ hmu hlam0 hmu0)

omit [CharP F 2] in
private lemma mat_cornerD_inv (hσ : IsUnitaryInvolution σ) (m : ℕ) {lam mu : F}
    (hmu : mu = σ lam) (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    mat σ (m + 4) ((cornerD hσ m lam mu hmu hlam0 hmu0)⁻¹) =
      diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by
  rw [cornerD]
  exact mat_diagSU_inv m F σ (diagT m F σ lam mu)
    (diagT_unitary m F σ hσ hlam0 hmu0) (diagT_prod m F σ hσ hmu hlam0 hmu0)

private lemma mat_cornerX0 (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) :
    mat σ (m + 4) (cornerX0 hσ m l) = 1 + nilSplit m l F + cornerX m F := by
  rw [cornerX0]
  exact mat_conj_cornerG1 hσ m l hl h2l

private lemma cornerLam_conj_cornerA (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) :
    cornerLam m F * (1 + nilSplit m l F + cornerX m F) * cornerLam m F =
      1 + nilSplit m l F + cornerX m F + single (corner1 m) (corner0 m) 1 +
        single (corner3 m) (corner2 m) 1 := by
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    Matrix.mul_one, cornerLam_mul_self hσ m,
    cornerLam_mul_nilSplit m l hl h2l, nilSplit_mul_cornerLam m l hl h2l,
    cornerLam_mul_cornerX_mul_cornerLam m F]
  abel

omit [CharP F 2] in
private lemma diagonal_conj_cornerA_main (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) {lam mu : F} (_hmu : mu = σ lam) (hlam0 : lam ≠ 0)
    (hmu0 : mu ≠ 0) :
    diagonal (diagT m F σ lam mu) *
        (1 + nilSplit m l F + cornerX m F + single (corner1 m) (corner0 m) 1 +
          single (corner3 m) (corner2 m) 1) *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) =
      1 + nilSplit m l F + diagonal (diagT m F σ lam mu) *
        (cornerX m F + single (corner1 m) (corner0 m) 1 +
          single (corner3 m) (corner2 m) 1) *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by
  have ht : ∀ k, ¬ (k = corner0 m ∨ k = corner1 m ∨ k = corner2 m ∨ k = corner3 m) →
      diagT m F σ lam mu k = 1 :=
    fun k hk => diagT_apply_of_not_corner m F σ lam mu hk
  have hD : diagonal (diagT m F σ lam mu) *
      diagonal (fun k => (diagT m F σ lam mu k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ ((ne_zero_of_unitary (diagT_unitary m F σ hσ hlam0 hmu0)) k)
  calc diagonal (diagT m F σ lam mu) *
        (1 + nilSplit m l F + cornerX m F + single (corner1 m) (corner0 m) 1 +
          single (corner3 m) (corner2 m) 1) *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹)
      = diagonal (diagT m F σ lam mu) * 1 * diagonal (fun k => (diagT m F σ lam mu k)⁻¹) +
          diagonal (diagT m F σ lam mu) * nilSplit m l F *
            diagonal (fun k => (diagT m F σ lam mu k)⁻¹) +
          diagonal (diagT m F σ lam mu) *
            (cornerX m F + single (corner1 m) (corner0 m) 1 +
              single (corner3 m) (corner2 m) 1) *
            diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by noncomm_ring
    _ = 1 + nilSplit m l F + diagonal (diagT m F σ lam mu) *
          (cornerX m F + single (corner1 m) (corner0 m) 1 +
            single (corner3 m) (corner2 m) 1) *
          diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by
      rw [Matrix.mul_one, hD, diagonal_mul_nilSplit_mul_diagonal_inv m l hl h2l _ ht]

omit [CharP F 2] in
private lemma diagonal_conj_cornerA (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) {lam mu : F} (hmu : mu = σ lam) (hlam0 : lam ≠ 0)
    (hmu0 : mu ≠ 0) :
    diagonal (diagT m F σ lam mu) *
        (1 + nilSplit m l F + cornerX m F + single (corner1 m) (corner0 m) 1 +
          single (corner3 m) (corner2 m) 1) *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹) =
      1 + nilSplit m l F + cornerY m F lam mu := by
  rw [diagonal_conj_cornerA_main hσ m l hl h2l hmu hlam0 hmu0]
  calc 1 + nilSplit m l F + diagonal (diagT m F σ lam mu) *
        (cornerX m F + single (corner1 m) (corner0 m) 1 +
          single (corner3 m) (corner2 m) 1) *
        diagonal (fun k => (diagT m F σ lam mu k)⁻¹)
      = 1 + nilSplit m l F +
          (diagonal (diagT m F σ lam mu) * cornerX m F *
              diagonal (fun k => (diagT m F σ lam mu k)⁻¹) +
            diagonal (diagT m F σ lam mu) * single (corner1 m) (corner0 m) 1 *
              diagonal (fun k => (diagT m F σ lam mu k)⁻¹) +
            diagonal (diagT m F σ lam mu) * single (corner3 m) (corner2 m) 1 *
              diagonal (fun k => (diagT m F σ lam mu k)⁻¹)) := by noncomm_ring
    _ = 1 + nilSplit m l F +
          ((single (corner3 m) (corner0 m) (mu * lam) +
              single (corner2 m) (corner0 m) (lam * lam) +
              single (corner3 m) (corner1 m) (mu * mu)) +
            single (corner1 m) (corner0 m) (lam / mu) +
            single (corner3 m) (corner2 m) (mu / lam)) := by
      rw [diagonal_mul_cornerX_mul_diagonal_inv m F σ hσ hmu,
        diagonal_mul_cornerE10_mul_diagonal_inv m F σ hσ hmu,
        diagonal_mul_cornerE32_mul_diagonal_inv m F σ hσ hmu]
    _ = 1 + nilSplit m l F + cornerY m F lam mu := by
      rw [cornerY]

private lemma mat_cornerY0 (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) {lam mu : F} (hmu : mu = σ lam) (hlam0 : lam ≠ 0)
    (hmu0 : mu ≠ 0) :
    mat σ (m + 4) (cornerY0 hσ m l lam mu hmu hlam0 hmu0) =
      1 + nilSplit m l F + cornerY m F lam mu := by
  have hDL : mat σ (m + 4) (cornerD hσ m lam mu hmu hlam0 hmu0 * cornerL hσ m) =
      diagonal (diagT m F σ lam mu) * cornerLam m F := by
    rw [map_mul, mat_cornerD, mat_cornerL]
  have hDLinv : mat σ (m + 4)
      ((cornerD hσ m lam mu hmu hlam0 hmu0 * cornerL hσ m)⁻¹) =
      cornerLam m F * diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (cornerL_mul_self hσ m), map_mul,
      mat_cornerL, mat_cornerD_inv]
  rw [cornerY0, map_mul, map_mul, hDL, hDLinv, mat_cornerX0 hσ m l hl h2l]
  calc (diagonal (diagT m F σ lam mu) * cornerLam m F) * (1 + nilSplit m l F + cornerX m F) *
        (cornerLam m F * diagonal (fun k => (diagT m F σ lam mu k)⁻¹))
      = diagonal (diagT m F σ lam mu) *
          (cornerLam m F * (1 + nilSplit m l F + cornerX m F) * cornerLam m F) *
          diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by noncomm_ring
    _ = diagonal (diagT m F σ lam mu) *
          (1 + nilSplit m l F + cornerX m F + single (corner1 m) (corner0 m) 1 +
            single (corner3 m) (corner2 m) 1) *
          diagonal (fun k => (diagT m F σ lam mu k)⁻¹) := by
      rw [cornerLam_conj_cornerA hσ m l hl h2l]
    _ = 1 + nilSplit m l F + cornerY m F lam mu :=
      diagonal_conj_cornerA hσ m l hl h2l hmu hlam0 hmu0

omit [CharP F 2] in
private lemma cornerX_mul_nilSplit (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) :
    cornerX m F * nilSplit m l F = 0 := by
  have h1 : single (corner3 m) (corner0 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (corner3 m) (Or.inl rfl) 1
  have h2 : single (corner2 m) (corner0 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (corner2 m) (Or.inl rfl) 1
  have h3 : single (corner3 m) (corner1 m) 1 * nilSplit m l F = 0 :=
    single_mul_nilSplit_corner (F := F) m hl h2l (corner3 m) (Or.inr (Or.inl rfl)) 1
  rw [cornerX, cornerE, cornerE, cornerE, Matrix.add_mul, Matrix.add_mul, h1, h2, h3]
  abel

omit [CharP F 2] in
private lemma nilSplit_mul_cornerY (m l : ℕ) (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4)
    (lam mu : F) : nilSplit m l F * cornerY m F lam mu = 0 := by
  have h1 := nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inr (Or.inr rfl)))
    (corner0 m) (mu * lam)
  have h2 := nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inr (Or.inl rfl)))
    (corner0 m) (lam * lam)
  have h3 := nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inr (Or.inr rfl)))
    (corner1 m) (mu * mu)
  have h4 := nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inl rfl))
    (corner0 m) (lam / mu)
  have h5 := nilSplit_mul_single_corner (F := F) m hl h2l (Or.inr (Or.inr (Or.inr rfl)))
    (corner2 m) (mu / lam)
  rw [cornerY, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
    h1, h2, h3, h4, h5]
  abel

private def cornerA (m : ℕ) (F : Type) [Field F] (lam mu : F) :
    Matrix (Fin (m + 4)) (Fin (m + 4)) F :=
  cornerX m F + cornerY m F lam mu + single (corner3 m) (corner0 m) (lam / mu)

private lemma cornerA_mul_self (m : ℕ) (F : Type) [Field F] [CharP F 2] {lam mu : F}
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    cornerA m F lam mu * cornerA m F lam mu =
      single (corner3 m) (corner0 m) (lam / mu + mu / lam) := by
  rw [cornerA]
  calc (cornerX m F + cornerY m F lam mu + single (corner3 m) (corner0 m) (lam / mu)) *
        (cornerX m F + cornerY m F lam mu + single (corner3 m) (corner0 m) (lam / mu))
      = cornerX m F * cornerX m F + cornerX m F * cornerY m F lam mu +
          cornerX m F * single (corner3 m) (corner0 m) (lam / mu) +
          cornerY m F lam mu * cornerX m F + cornerY m F lam mu * cornerY m F lam mu +
          cornerY m F lam mu * single (corner3 m) (corner0 m) (lam / mu) +
          single (corner3 m) (corner0 m) (lam / mu) * cornerX m F +
          single (corner3 m) (corner0 m) (lam / mu) * cornerY m F lam mu +
          single (corner3 m) (corner0 m) (lam / mu) *
            single (corner3 m) (corner0 m) (lam / mu) := by noncomm_ring
    _ = single (corner3 m) (corner0 m) (lam / mu) +
          single (corner3 m) (corner0 m) (mu / lam) := by
      rw [cornerX_mul_cornerX m F, cornerX_mul_cornerY m F lam mu,
        cornerX_mul_cornerE30 m F (lam / mu), cornerY_mul_cornerX m F lam mu,
        cornerY_mul_cornerY m F hlam0 hmu0, cornerY_mul_cornerE30 m F (lam / mu) lam mu,
        cornerE30_mul_cornerX m F (lam / mu), cornerE30_mul_cornerY m F (lam / mu) lam mu,
        cornerE30_mul_cornerE30 m F (lam / mu) (lam / mu)]
      abel
    _ = single (corner3 m) (corner0 m) (lam / mu + mu / lam) := by
      rw [← Matrix.single_add]

private lemma one_add_cornerA_mul_self (m : ℕ) (F : Type) [Field F] [CharP F 2] {lam mu : F}
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    (1 + cornerA m F lam mu) * (1 + cornerA m F lam mu) =
      1 + single (corner3 m) (corner0 m) (lam / mu + mu / lam) := by
  have h : (1 + cornerA m F lam mu) * (1 + cornerA m F lam mu) =
      1 + cornerA m F lam mu * cornerA m F lam mu := by
    calc (1 + cornerA m F lam mu) * (1 + cornerA m F lam mu)
        = 1 + (cornerA m F lam mu + cornerA m F lam mu) +
            cornerA m F lam mu * cornerA m F lam mu := by noncomm_ring
      _ = 1 + cornerA m F lam mu * cornerA m F lam mu := by
        rw [CharTwo.add_self_eq_zero, add_zero]
  rw [h, cornerA_mul_self m F hlam0 hmu0]

private lemma mat_cornerX0_mul_cornerY0 (hσ : IsUnitaryInvolution σ) (m l : ℕ) (hl : 2 ≤ l)
    (h2l : 2 * l ≤ m + 4) {lam mu : F} (hmu : mu = σ lam) (hlam0 : lam ≠ 0)
    (hmu0 : mu ≠ 0) :
    mat σ (m + 4) (cornerX0 hσ m l * cornerY0 hσ m l lam mu hmu hlam0 hmu0) =
      1 + cornerA m F lam mu := by
  rw [map_mul, mat_cornerX0 hσ m l hl h2l, mat_cornerY0 hσ m l hl h2l hmu hlam0 hmu0,
    cornerA]
  have h1 : (1 + nilSplit m l F + cornerX m F) *
      (1 + nilSplit m l F + cornerY m F lam mu) =
      1 + nilSplit m l F + cornerY m F lam mu + nilSplit m l F +
        nilSplit m l F * nilSplit m l F + nilSplit m l F * cornerY m F lam mu +
        cornerX m F + cornerX m F * nilSplit m l F +
        cornerX m F * cornerY m F lam mu := by noncomm_ring
  rw [h1, nilSplit_mul_self m hl h2l, nilSplit_mul_cornerY m l hl h2l lam mu,
    cornerX_mul_nilSplit m l hl h2l, cornerX_mul_cornerY m F lam mu]
  simp only [add_zero]
  calc 1 + nilSplit m l F + cornerY m F lam mu + nilSplit m l F + cornerX m F +
        single (corner3 m) (corner0 m) (lam / mu) =
      1 + (cornerX m F + cornerY m F lam mu + single (corner3 m) (corner0 m) (lam / mu)) +
        (nilSplit m l F + nilSplit m l F) := by abel
    _ = 1 + (cornerX m F + cornerY m F lam mu + single (corner3 m) (corner0 m) (lam / mu)) := by
      rw [CharTwo.add_self_eq_zero, add_zero]

private lemma mat_cornerX0_mul_cornerY0_sq (hσ : IsUnitaryInvolution σ) (m l : ℕ)
    (hl : 2 ≤ l) (h2l : 2 * l ≤ m + 4) {lam mu : F} (hmu : mu = σ lam)
    (hlam0 : lam ≠ 0) (hmu0 : mu ≠ 0) :
    mat σ (m + 4) ((cornerX0 hσ m l * cornerY0 hσ m l lam mu hmu hlam0 hmu0) ^ 2) =
      1 + single (corner3 m) (corner0 m) (lam / mu + mu / lam) := by
  rw [pow_two, map_mul, mat_cornerX0_mul_cornerY0 hσ m l hl h2l hmu hlam0 hmu0,
    one_add_cornerA_mul_self m F hlam0 hmu0]

theorem exists_isConj_ggInvSU_mul_sq_eq (hσ : IsUnitaryInvolution σ) {l : ℕ} (hl : 2 ≤ l)
    (h2l : 2 * l ≤ n) :
    ∃ x y : SU σ n, IsConj (ggInvSU σ n l) x ∧ IsConj (ggInvSU σ n l) y ∧
      ∃ c : F, c ≠ 0 ∧ mat σ n ((x * y) ^ 2) = 1 + c • ggInvUNil n 1 F := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  obtain ⟨lam, hlam⟩ := hσ.exists_ne
  let mu := σ lam
  have hmu : mu = σ lam := rfl
  have hlam0 : lam ≠ 0 := by
    intro h0
    exact hlam (by rw [h0, map_zero])
  have hmu0 : mu ≠ 0 := by
    rw [hmu]
    exact (map_ne_zero σ).mpr hlam0
  let x := cornerX0 hσ m l
  let y := cornerY0 hσ m l lam mu hmu hlam0 hmu0
  refine ⟨x, y, ?_, ?_, lam / mu + mu / lam, ?_, ?_⟩
  · exact isConj_iff.mpr ⟨cornerG1 hσ m, rfl⟩
  · refine isConj_iff.mpr ⟨(cornerD hσ m lam mu hmu hlam0 hmu0 * cornerL hσ m) *
      cornerG1 hσ m, ?_⟩
    dsimp [x, y, cornerX0, cornerY0]
    group
  · intro hzero
    have hprod : (lam / mu + mu / lam) * (lam * mu) = 0 := by rw [hzero, zero_mul]
    have hnum : lam * lam + mu * mu = 0 := by
      field_simp [hlam0, hmu0] at hprod
      simpa [pow_two] using hprod
    have hcross : lam * mu + lam * mu = 0 := CharTwo.add_self_eq_zero _
    have hsq : (lam + mu) * (lam + mu) = 0 := by
      calc (lam + mu) * (lam + mu) = lam * lam + mu * mu + (lam * mu + lam * mu) := by ring
        _ = lam * lam + mu * mu := by rw [hcross, add_zero]
        _ = 0 := hnum
    have hsum : lam + mu = 0 := mul_self_eq_zero.mp hsq
    have hlm : lam = mu := by
      have hneg := add_eq_zero_iff_eq_neg.mp hsum
      rwa [CharTwo.neg_eq] at hneg
    exact hlam (hmu.symm.trans hlm.symm)
  · rw [mat_cornerX0_mul_cornerY0_sq hσ m l hl h2l hmu hlam0 hmu0,
      ggInvUNil_one (F := F), Matrix.smul_single, smul_eq_mul, mul_one]

omit [CharP F 2] in
private lemma rank_smul_ggInvUNil {l : ℕ} (h : 2 * l ≤ n) {c : F} (hc : c ≠ 0) :
    (c • ggInvUNil n l F).rank = l := by
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
    rank_ggInvUNil h]

private lemma orderOf_mul_eq_four_and_sq_ne_one {x y : SU σ n} {c : F}
    (h21 : 2 * 1 ≤ n) (hc : c ≠ 0)
    (hmat : mat σ n ((x * y) ^ 2) = 1 + c • ggInvUNil n 1 F) :
    orderOf (x * y) = 4 ∧ (x * y) ^ 2 ≠ 1 := by
  have hsq : (mat σ n ((x * y) ^ 2)) ^ 2 = 1 := by
    rw [hmat, pow_two]
    have hX : (c • ggInvUNil n 1 F) + (c • ggInvUNil n 1 F) = 0 := by
      ext a b
      simpa using CharTwo.add_self_eq_zero ((c • ggInvUNil n 1 F) a b)
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, add_assoc,
      ← add_assoc (c • ggInvUNil n 1 F) (c • ggInvUNil n 1 F), hX, zero_add,
      smul_mul_smul_comm, ggInvUNil_mul_self, smul_zero, add_zero]
  have h4 : (x * y) ^ 4 = 1 := by
    have h2 : mat σ n (((x * y) ^ 2) ^ 2) = mat σ n 1 := by
      rw [map_pow, hsq, map_one]
    rw [show ((x * y) ^ 2) ^ 2 = (x * y) ^ 4 by rw [← pow_mul]] at h2
    exact mat_injective h2
  have hw2ne : (x * y) ^ 2 ≠ 1 := by
    intro hw
    have hcN : c • ggInvUNil n 1 F = 0 := by
      have h1 : (1 : Matrix (Fin n) (Fin n) F) + c • ggInvUNil n 1 F = 1 := by
        rw [← hmat, hw, map_one]
      have h1' : (1 : Matrix (Fin n) (Fin n) F) + c • ggInvUNil n 1 F = 1 + 0 := by
        simpa using h1
      exact add_left_cancel h1'
    have hN0 : ggInvUNil n 1 F = 0 := by
      rcases smul_eq_zero.mp hcN with hc' | hN
      · exact absurd hc' hc
      · exact hN
    have hrank := rank_smul_ggInvUNil (l := 1) h21 hc
    rw [hN0, smul_zero] at hrank
    simp at hrank
  have hord : orderOf (x * y) = 4 := by
    have hnot : ¬ (x * y) ^ 2 ^ 1 = 1 := by simpa using hw2ne
    have hfin : (x * y) ^ 2 ^ (1 + 1) = 1 := by simpa using h4
    simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
  exact ⟨hord, hw2ne⟩

private lemma false_of_isConj_ggInvSU_sq {l : ℕ} {x y : SU σ n} {c : F}
    (hconj : IsConj (ggInvSU σ n l) ((x * y) ^ 2)) (hl : 1 < l) (h2l : 2 * l ≤ n)
    (h21 : 2 * 1 ≤ n) (hc : c ≠ 0)
    (hmat : mat σ n ((x * y) ^ 2) = 1 + c • ggInvUNil n 1 F) : False := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hrank_eq : (mat σ n ((x * y) ^ 2) - 1).rank = l := by
    rw [← hg, rank_mat_conj_sub_one g (ggInvSU σ n l), rank_mat_ggInvSU_sub_one h2l]
  have hrank_one : (mat σ n ((x * y) ^ 2) - 1).rank = 1 := by
    rw [hmat, add_sub_cancel_left, rank_smul_ggInvUNil (l := 1) h21 hc]
  omega

theorem isConj_ggInvSU_one_of_isConj_sq [Finite F] (hσ : IsUnitaryInvolution σ) {u : SU σ n}
    (hu : orderOf u = 2)
    (h : ∀ x y : SU σ n, IsConj u x → IsConj u y → orderOf (x * y) = 4 → IsConj ((x * y) ^ 2) u) :
    IsConj (ggInvSU σ n 1) u := by
  obtain ⟨l, hl1, h2l, a, ha⟩ := exists_conj_ggInvSU_of_orderOf_eq_two hσ hu
  rcases eq_or_lt_of_le hl1 with rfl | hl
  · exact isConj_iff.mpr ⟨a, ha.symm⟩
  have h21 : 2 * 1 ≤ n := (Nat.mul_le_mul_left 2 (le_of_lt hl)).trans h2l
  obtain ⟨x, y, hx, hy, c, hc0, hmat⟩ :=
    exists_isConj_ggInvSU_mul_sq_eq hσ (by omega) h2l
  have hconj₀ : IsConj (ggInvSU σ n l) u := isConj_iff.mpr ⟨a, ha.symm⟩
  have hux : IsConj u x := hconj₀.symm.trans hx
  have huy : IsConj u y := hconj₀.symm.trans hy
  obtain ⟨hord, -⟩ := orderOf_mul_eq_four_and_sq_ne_one h21 hc0 hmat
  have hconj : IsConj (ggInvSU σ n l) ((x * y) ^ 2) :=
    hconj₀.trans (h x y hux huy hord).symm
  exact False.elim (false_of_isConj_ggInvSU_sq hconj hl h2l h21 hc0 hmat)

end CFSG.StandardType.SUTransvection
