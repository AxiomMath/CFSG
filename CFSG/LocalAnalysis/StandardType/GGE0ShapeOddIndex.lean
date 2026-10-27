module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree

theorem twisted_root_kill
    {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (h2 : ringChar K = 2)
    (A : Subgroup (ModGL TwistTag.E6.tag K))
    (hAI : A ≤ twistedE6InndiagGL K σ) (hodd : Odd (Nat.card A))
    (hU : TwE6RootKill.TwNormTwo K σ A)
    (D : TwLangData K σ q A) (hlong : TwE6RootKill.IsLongest D.v) :
    ∃ α, IsRoot TwistTag.E6.tag α ∧ TwE6RootKill.TwDataKills D α :=
  TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
    TwE6RootKill.ennolaSplitStep_holds K σ q hK hσ h2 A hAI hodd hU D hlong

end CFSG.StandardType
