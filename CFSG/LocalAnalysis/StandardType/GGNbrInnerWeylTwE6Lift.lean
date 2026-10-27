module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerInput
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Main

theorem ggTorusLift_twE6Add_holds {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusLift p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) :=
  TwE6Per.ggTwE6TorusLiftInput_holds K n p hn hK hp hpn

theorem largeEvenLabelAll_torusLift_twE6Add_holds {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (TwE6Delta.liftRank p) R :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK =>
    ggTorusLift_twE6Add_holds hlab.1 hK hp h.2

end Main

end CFSG.StandardType

end
