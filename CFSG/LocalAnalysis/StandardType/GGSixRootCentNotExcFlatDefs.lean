module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcRows
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGRootCentAutKNotExcFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J →
      (∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → ⁅P, P⁆ = P →
        P ≤ ggG0 p B x L D J) →
      ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
      (∃ o ∈ ggRootFactorOrders t n f, GGInvolCentTypedBy (ggG0 p B x L D J) r o) →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
          GGRCSAutKIIIFlat (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K →
          GGRCSAutKIVFlat p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K →
            GGRCSAutKNotExc p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

theorem ggRootCentAutKNotExcInput_of_flat_count (hcount : ∀ t, GGRootInvolCountTag t)
    (hSP : GGSchreierPerfectInput) (hN : GGRootCentAutKNotExcFlatInput)
    (h3 : GGRootCentAutKIIIFlatInput) (h4 : GGRootCentAutKIVFlatInput) :
    GGRootCentAutKNotExcInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset _ hsh
  exact hN G p B Bs x L D J t n f ψ hctx s1 s2 (ggSixSchreier_of_ctx hSP hctx s1) E r hch
    (ggSixRootCent_exists_count_of_ctx (hcount t) hctx s1 hch) K S hset
    (h3 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)
    (h4 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset) hsh

end Inputs

end CFSG.StandardType
