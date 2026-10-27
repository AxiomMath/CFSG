module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_M22HexadPair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    IsSpor (↥K ⧸ Subgroup.center ↥K) .M22 →
    ∃ E X₁ X₂ : Subgroup Y,
      E ≤ K ∧ Nat.card E = 9 ∧ IsElemAbelian 3 E ∧
        X₁ ≤ K ∧ X₂ ≤ K ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
          Permutes X₁ S ∧ Permutes X₂ S ∧ E ≤ X₁ ⊔ X₂ ⊔ S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
