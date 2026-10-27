module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def W3Thm172Weak (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (D : Data G) (V₀ V : Subgroup G), WeakClosureSetting D V₀ V → V₀ ≠ ⊥ →
    ∀ H : Subgroup G, W3Hyp171 D H → IsSolvable ↥H → MBarGT D.M V₀ V 2 →
      normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M → H ≤ D.M

end CFSG.LocalAnalysis.WeakClosure81

end
