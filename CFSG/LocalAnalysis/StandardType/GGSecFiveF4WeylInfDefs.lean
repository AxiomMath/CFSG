module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveF4ReflSatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
          ∀ (hx : x ∈ Bs) (φ : MulAut ↥Bs), φ ∈ ggAInf p B Bs x L D J → GGIsReflection p φ →
            φ ⟨x, hx⟩ = ⟨x, hx⟩ → φ ∈ ggAutomizerJoin L Bs 𝒦

end CFSG.StandardType

end
