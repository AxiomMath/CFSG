module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def WeylGoodRankFive (Ω : Type) [Field Ω] : Prop :=
  ∀ {ι : Type} (a : ι → Fin Tag.E6.rank → Ωˣ), (∀ i j, a i j ^ 3 = 1) →
    3 ^ 5 ≤ Nat.card (Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i))) →
      WeylGood (τ := Tag.E6) a

end CFSG.StandardType
