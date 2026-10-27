module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTriD4InnerCompInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → (n = 1 ∨ 3 ∣ 2 ^ n - 1) → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ n) ^ 3 → ∀ h : GGTriD4R n K, h ≠ 1 → h ^ 3 = 1 →
      ∀ Q : Subgroup (GGTriD4R n K), IsComponentOf Q (Subgroup.centralizer ({h} : Set _)) →
        (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ n) ^ 3 ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
        (2 ≤ n ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 2 ^ n ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)))

end CFSG.StandardType
