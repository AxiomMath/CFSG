module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

@[expose] def K326P2S : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → CFSG.pPrimeCore 3 G = ⊥ →
    ∀ n : ℕ, 1 ≤ n → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
    Nonempty (↥P ≃* ZWr n) → OmegaCentral P →
    ∀ (M : Subgroup G) (a : G), a ∈ jOf P → a ∉ z2Of P →
      Subgroup.normalizer (jOf P : Set G) ⊔ Subgroup.centralizer ({a} : Set G) ≤ M →
        M = ⊤ ∨ (n = 1 ∧ Nat.card (CFSG.pCore 3 G) = 27 ∧
          Nat.card (CFSG.GH74.GLS.oPrimeResidual 3 G) = 648 ∧
          CFSG.pCore 3 G ≤ CFSG.GH74.GLS.oPrimeResidual 3 G)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
