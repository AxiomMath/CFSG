module

public import CFSG.LocalAnalysis.StandardType.TableC.Hyp

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

@[expose] def GGTCTwE6AtLe
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B D J L : Subgroup X) (x : X), GGTCHyp .twistedE6 n f ψ p G₀ B D J L x →
      GGSixLSevenFieldExtCase J .twistedE6 f →
        GGSixTCResidual p L J f ∧ Nat.card B = 3 ^ 4 ∧
          ∀ R : Subgroup X, IsPGroup 2 R → R ≤ G₀ →
            B ≤ Subgroup.normalizer (R : Set X) → R = ⊥

theorem ggSixFieldExtTableCTwistedE6Res_of_tcLe
    (h : GGTCTwE6AtLe) :
    GGSixFieldExtTableCTwistedE6Res := by
  intro G _ _ p B Bs x L D J n f ψ hc hD hodd hcomp hz _ _ hF
  exact h G n f ψ p _ B D J L x (ggTCHyp_of_ctx ⟨hc, hD, hodd, hcomp, hz⟩) hF

end CFSG.StandardType.TableCRes

end
