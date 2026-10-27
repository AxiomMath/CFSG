module

public import CFSG.LieType.Sp6Spin.FixedPointFree
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118CMSp

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem cmSpStructure_holds : CMSpStructure :=
  cmSpStructure_of_spinFPF fun K _ _ _ V _ _ _ Qf hK hV hQ ψ hψ hirr _ =>
    CFSG.LieType.Sp6Spin.exists_odd_orderOf_fixedPointFree K V Qf hK hV hQ ψ hψ hirr

end CFSG.RankThree.GF2n.Stroth80
