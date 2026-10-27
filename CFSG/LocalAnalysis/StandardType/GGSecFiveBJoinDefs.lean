module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

@[expose] def GGResNbrFixCentralizesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G)

@[expose] def BMaxJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixB M →
          (∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
            ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

end CFSG.StandardType

end
