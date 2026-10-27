module

public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import CFSG.LieType.ChevTwo.OrthogonalAutEquiv

public section

namespace CFSG.RankThree.GF2n.Tim79a

theorem oMinusSixTwoAutPSp43Statement_holds : OMinusSixTwoAutPSp43Statement :=
  ⟨_, inferInstance, CFSG.LieType.ChevTwo.lieModel_statedOmega_quadMinus_three_two,
    CFSG.LieType.ChevTwo.nonempty_orthogonalGroup_quadMinus_three_two_equiv_mulAut⟩

end CFSG.RankThree.GF2n.Tim79a
