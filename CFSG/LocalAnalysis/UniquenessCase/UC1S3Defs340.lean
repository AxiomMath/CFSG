module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

@[expose] def K340 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L T F V X : Subgroup G) (n : ℕ),
    Fstar H = CFSG.Open.pCoreOf 2 H → L = CFSG.Quasithin.opResidual 2 H →
    IsL2 (Bar2 L) n → CFSG.ABGLocalTools.IsSylowOf 2 T H → H = T ⊔ L →
    T ≤ L ⊔ CFSG.Open.pCoreOf 2 H →
    ¬ CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ (Subgroup.center ↥H).map H.subtype →
    F = omegaOneZJ (CFSG.Open.pCoreOf 2 H) →
    V = ⁅L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆ →
    F ≤ thompsonJ T → V ≤ thompsonJ T →
    X ≤ Subgroup.normalizer (thompsonJ T : Set G) → thompsonJ H ⊓ T ≤ X →
      thompsonJ H ≤ Subgroup.normalizer (conjClosure X F : Set G) ∨
      ∃ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ ≠ ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
