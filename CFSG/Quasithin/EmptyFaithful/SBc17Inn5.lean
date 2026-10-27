module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases
public import CFSG.Quasithin.EmptyFaithful.SBc17N2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace SBc17

@[expose] def Input14615ContraInnerF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ASC27Statement G →
    ∀ (T M : Subgroup G), Setting146 G T M →
      ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
        ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
          ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
            ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
              HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
                CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                  ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                      ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 →
                        K₁ ≤ Subgroup.normalizer (J : Set G) →
                          K₂ ≤ Subgroup.normalizer (J : Set G) →
                            ⁅J, K₂⁆ ≤ pCoreOf 2 J → pCoreOf 2 J ≤ mcOf T →
                              K₁ ⊔ K₂ ≤ innerSub J → g2_14615 K₂ ≤ Subgroup.normalizer (J : Set G) →
                                (∃ a ∈ J, orderOf a = 5) → K₁ ≤ J →
                                  quasithinOmegaOneCenter T ≤ J ⊓ g12_14615 T K₂ →
                                    ¬ IsL2BorelBlock J (J ⊓ g12_14615 T K₂) →
                                      C27SL3 (g2_14615 K₂) (pCoreOf 2 (mcOf T))
                                        (g12_14615 T K₂) J
                                        (omegaOneCenterOf (pCoreOf 2 (J ⊔ pCoreOf 2 (mcOf T)))) →
                                        False

end SBc17

end CFSG.Quasithin
