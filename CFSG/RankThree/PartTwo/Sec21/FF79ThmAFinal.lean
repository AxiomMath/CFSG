module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def FF79Concl35 (b : G) (A : Subgroup G) : Prop :=
  ∃ U₁ U₂ : Subgroup G, IsElemAb 3 2 U₁ ∧ IsElemAb 3 2 U₂ ∧ U₁ ⊔ U₂ = A ∧ U₁ ⊓ U₂ = ⊥ ∧
    b ∈ Nor U₁ ∧ b ∈ Nor U₂ ∧
    U₁ ≤ OppE 3 (CenS U₂) ∧ U₂ ≤ OppE 3 (CenS U₁) ∧
    IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS U₁ ⧸ pPrimeCore 3 (CenS U₁)))) ∧
    IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS U₂ ⧸ pPrimeCore 3 (CenS U₂)))) ∧
    IsLnq 2 2 2 (OUpp 2 (OppE 3 (CenS U₁) ⊓ Cen b)) ∧
    IsLnq 2 2 2 (OUpp 2 (OppE 3 (CenS U₂) ⊓ Cen b))

end CFSG.RankThree.PartTwo.Sec21.FF79
