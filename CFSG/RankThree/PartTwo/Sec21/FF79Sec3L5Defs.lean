module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FF79KL35a : Prop :=
  ∀ (E : Type) [Group E] [Finite E], StatedClassicalModel E .PSL 3 2 2 →
    ∀ β : MulAut E, β ^ 3 = 1 → ∀ S : Subgroup E, Nat.card S = 9 → (∀ s ∈ S, β s ∈ S) →
      (∃ K : Subgroup E, StatedClassicalModel K .PSL 2 2 2 ∧ ∀ x ∈ K, β x = x) →
      ∃ σ : E, orderOf σ = 2 ∧ β σ = σ ∧ ∀ s ∈ S, σ * s * σ⁻¹ = s⁻¹

@[expose] def FF79KL35b : Prop :=
  ∀ (E : Type) [Group E] [Finite E], StatedClassicalModel E .PSL 3 2 2 →
    ∀ β : MulAut E, β ^ 3 = 1 → (∀ e : E, β ≠ MulAut.conj e) →
      ∀ K : Subgroup E, StatedClassicalModel K .PSL 2 2 2 → (∀ x ∈ K, β x = x) →
        ∀ g : E, β g = g → g ∈ K

variable {G : Type} [Group G] [Finite G]

@[expose] def FF79Sec35P (b : G) (U : Subgroup G) : Prop :=
  IsElemAb 3 2 U ∧ b ∈ Nor U ∧
    IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS U ⧸ pPrimeCore 3 (CenS U)))) ∧
    IsLnq 2 2 2 (OUpp 2 (OppE 3 (CenS U) ⊓ Cen b))

end CFSG.RankThree.PartTwo.Sec21.FF79
