module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def nontoralMaxRank (τ : Tag) (p : ℕ) : ℕ :=
  match τ with
  | .F4 => if p = 3 then 3 else 0
  | .E6 => if p = 3 then 4 else 0
  | .E7 => if p = 3 then 4 else 0
  | .E8 => if p = 3 then 5 else if p = 5 then 3 else 0
  | _ => 0

@[expose] def GGLieNonToralRankFour :
    Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (t : StatedLieTag), (t = .E6 ∧ Odd f) ∨ (t = .twistedE6 ∧ Even f) →
    ∀ A : Subgroup (ModGL (langTag t) GGL), A ≤ ratPoints (ggPhi t f) → IsElemAbelian 3 A →
      Nat.card A = 3 ^ 4 → IsToralSubgroup (langTag t) GGL A

end CFSG.StandardType.LieCore
