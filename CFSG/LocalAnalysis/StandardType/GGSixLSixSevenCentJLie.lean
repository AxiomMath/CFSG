module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCases

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSixLSixSevenCentJLieInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J t f →
      Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J

theorem ggSixCentralizerJInput_of_casesCentJ (h64 : GGSixCentreOddInput)
    (hA3 : GGSixLSixSevenConjA3Input) (hE6 : GGSixLSixSevenCentJE6Input)
    (hLie : GGSixLSixSevenCentJLieInput) : GGSixCentralizerJInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  by_cases hA : GGSixLSevenA3Case J
  · obtain ⟨g, hg, hDg⟩ := hA3 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp hA
    exact hctx.centralizer_le_ggM_of_conj hC2 hg hDg
  by_cases hE : GGSixLSevenE6Case p L J t f
  · exact hE6 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp hE
  exact hLie G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
    (h64 G p B Bs x L D J t n f ψ hctx hodd).2 hA hE

end Inputs

end CFSG.StandardType
