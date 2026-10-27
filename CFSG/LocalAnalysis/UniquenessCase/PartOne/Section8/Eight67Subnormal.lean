module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC6

theorem false_of_subnormal_InU_of_not_normalizer_le
    {G : Type} [Group G] [Finite G] {M X Y : Subgroup G}
    (hM : Subgroup.normalizer (M : Set G) = M)
    (hXY : CFSG.Open.IsSubnormal X Y)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC6.InU M X)
    (hHnotM : ¬ Subgroup.normalizer (Y : Set G) ≤ M) : False :=
  hHnotM ((InU.of_subnormal hM hXY hX).normalizer_le hM)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
