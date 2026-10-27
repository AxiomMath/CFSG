module

public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.KF.F128SU
public import CFSG.RankThree.PartOne.S11d.PSLRankTwo
public import CFSG.Quasithin.EmptyFaithful.R3c18B
public import CFSG.Quasithin.EmptyFaithful.R3c18C
public import CFSG.Quasithin.EmptyFaithful.R3c18E

public section

namespace CFSG.Quasithin

namespace R3c18

theorem sp4PRankShape_holds : Sp4PRankShape := by
  intro K _ _ p hp hp2 hpK h
  exact CFSG.RankThree.PartOne.pRank_statedSp_le_one (n := 2) hp hp2 hpK h

theorem l3PRankShape_holds : L3PRankShape := by
  intro K _ _ _ p e hp hp2 hpK he h2
  exact CFSG.RankThree.PartOne.two_mul_le_of_pRank_projectiveSL (n := 3) hp hp2 hpK he h2

theorem u3PRankShape_holds : U3PRankShape := by
  intro K _ _ p q hp hp2 hK hpq h
  exact CFSG.RankThree.PartOne.pRank_statedSU_le_one (n := 3) hp hp2 hK hpq (by norm_num) h

section Certificates

theorem g2PRankShape_holds : G2PRankShape := by
  intro K _ _ _ p m hp hp5 hK hm hd hnd
  exact CFSG.RankThree.PartOne.K128.pRank_le_one_G2 K hp hp5 hK hm hd hnd

end Certificates

end R3c18

end CFSG.Quasithin
