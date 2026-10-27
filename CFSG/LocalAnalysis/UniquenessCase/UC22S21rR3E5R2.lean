module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_22R3E5R2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    D.sig = D.sig1 → CFSG.Open.evenRank G = 3 → IsPowTwo c.n →
    ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → ∀ n : ℕ, 2 < n →
      ((IsSz (Bar2 L) n ∧ 3 ∣ n ∧ ∀ b ∈ c.B0, orderOf b = 3 → ∀ Y ∈ conjSetOf D.M L,
          ¬ ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) ∨
        (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n ∧ ∀ p ∈ D.sig, p ∣ n)) → False

end CFSG.LocalAnalysis.UniquenessCase.UC22
