module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveBFourPermExcInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixBFour M →
          ∀ hx : x ∈ Bs, (¬ ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧
              t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹) →
            ∀ eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)),
              (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p →
            ∀ k : ZS.ExcRow, (k = .N4 ∨ k = .EN4) → 4 ∣ p - 1 →
              (∃ f : ↥(ZS.model k) ≃* ↥(ggAInf p B Bs x L D J),
                ∀ g : ↥(ZS.model k), ZS.IsReflMat g.1 ↔ GGIsReflection p (f g : MulAut ↥Bs)) →
              (∀ s ∈ ggAInf p B Bs x L D J, ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p s →
                GGIsReflection p t → ∃ g ∈ ggAInf p B Bs x L D J, t = g * s * g⁻¹) →
              (∀ s ∈ ggAInf p B Bs x L D J, ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p s →
                GGIsReflection p t → orderOf (s * t) ≤ 4) →
              GGWeylReflectionGroup p (ggAInf p B Bs x L D J)

end CFSG.StandardType

end
