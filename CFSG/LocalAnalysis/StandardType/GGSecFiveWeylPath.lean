module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

private lemma natCard_eq_of_equiv_fin {ι : Type} {n : ℕ} (e : Fin n ≃ ι) : Nat.card ι = n := by
  rw [← Nat.card_congr e, Nat.card_fin]

theorem ggWeylMatrix_exists_path_of_rank {ι : Type} (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M)
    (hrank : 3 ≤ Nat.card ι) :
    ∃ a v b : ι, a ≠ b ∧ (M.M a v = 3 ∨ M.M a v = 4) ∧ (M.M v b = 3 ∨ M.M v b = 4) ∧ M.M a b = 2 ∧
      (M.M a v = 3 ∨ M.M v b = 3) := by
  rcases hM with ⟨n, e, _, hA | ⟨_, hB⟩ | ⟨_, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hG2⟩
  ·
    by_cases hn3 : 3 ≤ n
    · obtain ⟨h0, h1, h2⟩ : 0 < n ∧ 1 < n ∧ 2 < n := by omega
      refine ⟨e ⟨0, h0⟩, e ⟨1, h1⟩, e ⟨2, h2⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro hab
        have h02 : M.M (e ⟨0, h0⟩) (e ⟨2, h2⟩) = 2 := by
          rw [hA]
          simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.A,
            Matrix.of_apply]
        rw [hab] at h02
        simp at h02
      · left
        rw [hA]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.A,
          Matrix.of_apply]
      · left
        rw [hA]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.A,
          Matrix.of_apply]
      · rw [hA]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.A,
          Matrix.of_apply]
      · left
        rw [hA]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.A,
          Matrix.of_apply]
    · have hcardι : Nat.card ι = n := natCard_eq_of_equiv_fin e
      omega
  ·
    by_cases hn3 : 3 ≤ n
    · obtain ⟨h0, h1, h2⟩ : 0 < n ∧ 1 < n ∧ 2 < n := by omega
      refine ⟨e ⟨0, h0⟩, e ⟨1, h1⟩, e ⟨2, h2⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro hab
        have h02 : M.M (e ⟨0, h0⟩) (e ⟨2, h2⟩) = 2 := by
          rw [hB]
          simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
            Matrix.of_apply]
          omega
        rw [hab] at h02
        simp at h02
      · left
        rw [hB]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
          Matrix.of_apply]
        omega
      · rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
        · right
          rw [hB]
          simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
            Matrix.of_apply]
        · left
          rw [hB]
          simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
            Matrix.of_apply]
          omega
      · rw [hB]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
          Matrix.of_apply]
        omega
      · left
        rw [hB]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, CoxeterMatrix.B,
          Matrix.of_apply]
        omega
    · have hcardι : Nat.card ι = n := natCard_eq_of_equiv_fin e
      omega
  ·
    obtain ⟨h0, h1, h2⟩ : 0 < n ∧ 1 < n ∧ 2 < n := by omega
    refine ⟨e ⟨0, h0⟩, e ⟨1, h1⟩, e ⟨2, h2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab
      have h02 : M.M (e ⟨0, h0⟩) (e ⟨2, h2⟩) = 2 := by
        rw [hD, CoxeterMatrix.reindex_apply]
        simp only [Equiv.symm_apply_apply, ggCoxeterMatrixD_apply, CartanMatrix.D,
          Matrix.of_apply, Fin.mk.injEq]
        simp
        split_ifs <;> simp <;> omega
      rw [hab] at h02
      simp at h02
    · left
      rw [hD, CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply, ggCoxeterMatrixD_apply, CartanMatrix.D,
        Matrix.of_apply, Fin.mk.injEq]
      simp
      split_ifs <;> simp <;> omega
    · left
      rw [hD, CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply, ggCoxeterMatrixD_apply, CartanMatrix.D,
        Matrix.of_apply, Fin.mk.injEq]
      simp
      split_ifs <;> simp <;> omega
    · rw [hD, CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply, ggCoxeterMatrixD_apply, CartanMatrix.D,
        Matrix.of_apply, Fin.mk.injEq]
      simp
      split_ifs <;> simp <;> omega
    · left
      rw [hD, CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply, ggCoxeterMatrixD_apply, CartanMatrix.D,
        Matrix.of_apply, Fin.mk.injEq]
      simp
      split_ifs <;> simp <;> omega
  ·
    obtain ⟨h0, h2, h3⟩ : 0 < 6 ∧ 2 < 6 ∧ 3 < 6 := by norm_num
    refine ⟨e ⟨0, h0⟩, e ⟨2, h2⟩, e ⟨3, h3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab
      have h03 : M.M (e ⟨0, h0⟩) (e ⟨3, h3⟩) = 2 := by
        rw [hE6]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        decide
      rw [hab] at h03
      simp at h03
    · left; rw [hE6]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE6]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · rw [hE6]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE6]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
  ·
    obtain ⟨h0, h2, h3⟩ : 0 < 7 ∧ 2 < 7 ∧ 3 < 7 := by norm_num
    refine ⟨e ⟨0, h0⟩, e ⟨2, h2⟩, e ⟨3, h3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab
      have h03 : M.M (e ⟨0, h0⟩) (e ⟨3, h3⟩) = 2 := by
        rw [hE7]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        decide
      rw [hab] at h03
      simp at h03
    · left; rw [hE7]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE7]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · rw [hE7]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE7]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
  ·
    obtain ⟨h0, h2, h3⟩ : 0 < 8 ∧ 2 < 8 ∧ 3 < 8 := by norm_num
    refine ⟨e ⟨0, h0⟩, e ⟨2, h2⟩, e ⟨3, h3⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab
      have h03 : M.M (e ⟨0, h0⟩) (e ⟨3, h3⟩) = 2 := by
        rw [hE8]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        decide
      rw [hab] at h03
      simp at h03
    · left; rw [hE8]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE8]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · rw [hE8]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hE8]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
  ·
    obtain ⟨h0, h1, h2⟩ : 0 < 4 ∧ 1 < 4 ∧ 2 < 4 := by norm_num
    refine ⟨e ⟨0, h0⟩, e ⟨1, h1⟩, e ⟨2, h2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab
      have h02 : M.M (e ⟨0, h0⟩) (e ⟨2, h2⟩) = 2 := by
        rw [hF4]
        simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        decide
      rw [hab] at h02
      simp at h02
    · left; rw [hF4]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · right; rw [hF4]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · rw [hF4]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
    · left; rw [hF4]
      simp [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]; decide
  ·
    have hcardι : Nat.card ι = 2 := natCard_eq_of_equiv_fin e
    omega

end CFSG.StandardType

end
