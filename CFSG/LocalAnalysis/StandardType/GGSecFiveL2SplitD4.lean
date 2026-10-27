module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

@[expose] def ggD4Leaf : Fin 6 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![2, 1, 0, 3], ![3, 1, 2, 0], ![2, 1, 3, 0], ![3, 1, 0, 2]]

@[expose] def ggD4LeafInv : Fin 6 → Fin 6 := ![0, 1, 2, 3, 5, 4]

private def cox4 (y z : Fin 4) : ℕ := ggCoxeterMatrixD 4 y z

private theorem leaf_table :
    (∀ (m : Fin 6) (y : Fin 4), ggD4Leaf (ggD4LeafInv m) (ggD4Leaf m y) = y ∧
        ggD4Leaf m (ggD4Leaf (ggD4LeafInv m) y) = y) ∧
      (∀ (m : Fin 6) (y z : Fin 4), cox4 (ggD4Leaf m y) (ggD4Leaf m z) = cox4 y z) ∧
      ∀ a b : Fin 4, a ≠ b → cox4 a b = 2 → ∃ m : Fin 6, ggD4Leaf m 2 = a ∧ ggD4Leaf m 3 = b := by
  decide +kernel

theorem ggD4_leaf_table :
    (∀ (m : Fin 6) (y : Fin 4), ggD4Leaf (ggD4LeafInv m) (ggD4Leaf m y) = y ∧
        ggD4Leaf m (ggD4Leaf (ggD4LeafInv m) y) = y) ∧
      (∀ (m : Fin 6) (y z : Fin 4),
        ggCoxeterMatrixD 4 (ggD4Leaf m y) (ggD4Leaf m z) = ggCoxeterMatrixD 4 y z) ∧
      ∀ a b : Fin 4, a ≠ b → ggCoxeterMatrixD 4 a b = 2 →
        ∃ m : Fin 6, ggD4Leaf m 2 = a ∧ ggD4Leaf m 3 = b :=
  leaf_table

theorem ggD4_fork_of_label_two {a b : Fin 4} (hab : a ≠ b) (h2 : ggCoxeterMatrixD 4 a b = 2) :
    ∃ τ : Fin 4 ≃ Fin 4, (∀ x y, ggCoxeterMatrixD 4 (τ x) (τ y) = ggCoxeterMatrixD 4 x y) ∧
      τ 2 = a ∧ τ 3 = b := by
  obtain ⟨hinv, hpres, hex⟩ := ggD4_leaf_table
  obtain ⟨m, hma, hmb⟩ := hex a b hab h2
  exact ⟨⟨ggD4Leaf m, ggD4Leaf (ggD4LeafInv m), fun y => (hinv m y).1, fun y => (hinv m y).2⟩,
    hpres m, hma, hmb⟩

theorem ggD4_fork_numbering {ι : Type} {M : CoxeterMatrix ι} {σ : Fin 4 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 4).reindex σ) {i j : ι} (hij : i ≠ j) (h2 : M.M i j = 2) :
    ∃ σ' : Fin 4 ≃ ι, M = (ggCoxeterMatrixD 4).reindex σ' ∧ σ' 2 = i ∧ σ' 3 = j := by
  subst hM
  obtain ⟨τ, hτ, hτa, hτb⟩ := ggD4_fork_of_label_two (σ.symm.injective.ne hij) h2
  refine ⟨τ.trans σ, ?_, ?_, ?_⟩
  · ext x y
    rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, Equiv.symm_trans_apply,
      Equiv.symm_trans_apply, ← hτ (τ.symm (σ.symm x)) (τ.symm (σ.symm y)),
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rw [Equiv.trans_apply, hτa, Equiv.apply_symm_apply]
  · rw [Equiv.trans_apply, hτb, Equiv.apply_symm_apply]

end CFSG.StandardType

end
