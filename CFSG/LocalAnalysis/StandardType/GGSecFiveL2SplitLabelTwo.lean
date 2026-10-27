module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

private theorem entry_A {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : j.val = 2) :
    (CoxeterMatrix.A n).M i j = 2 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem entry_B {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : j.val = 2) :
    (CoxeterMatrix.B n).M i j = 2 := by
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  have hC : CartanMatrix.B n i j = 0 := by
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  rcases (ggIntCartan_B n).2 i j hij with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact h
  · rw [hC] at h
    omega
  · rw [hC, zero_mul] at h
    omega
  · rw [hC, zero_mul] at h
    omega

private theorem entry_D {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hi : i.val = 0) (hj : j.val = 2) :
    (ggCoxeterMatrixD n).M i j = 2 := by
  have h := ggCoxeterMatrixD_apply n i j
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h
  rw [h]
  split_ifs <;> omega

theorem ggWeylMatrix_exists_label_two {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hcard : 3 ≤ Nat.card ι) : ∃ a b : ι, a ≠ b ∧ M.M a b = 2 := by
  rcases hM with ⟨n, e, -, hX⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hF⟩ | ⟨e, hG⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    refine ⟨e ⟨0, by omega⟩, e ⟨2, by omega⟩, e.injective.ne (by simp), ?_⟩
    rcases hX with hA | ⟨-, hB⟩ | ⟨hn, hD⟩
    · rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact entry_A rfl rfl
    · rw [hB, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact entry_B rfl rfl
    · rw [hD, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact entry_D hn rfl rfl
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
    rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · refine ⟨e 0, e 2, e.injective.ne (by decide), ?_⟩
    rw [hF, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    omega

end CFSG.StandardType

end
