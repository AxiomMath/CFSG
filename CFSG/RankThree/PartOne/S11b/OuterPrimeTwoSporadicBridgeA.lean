module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22
import CFSG.Sporadic.Schreier.M23
import CFSG.Sporadic.Schreier.M24
import CFSG.Sporadic.Schreier.J1Outer
import CFSG.Sporadic.Schreier.PairJ2Pairs
import CFSG.Sporadic.Schreier.PairJ3Pairs
import CFSG.Sporadic.Schreier.PairHSPairs
import CFSG.Sporadic.SuzOddCore.Outer
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint

theorem sporadicOuterSmall_M11 : SporadicOuterSmall .M11 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m11_schreier.1 (by norm_num))

theorem sporadicOuterSmall_M12 : SporadicOuterSmall .M12 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m12_schreier.1 (by norm_num))

theorem sporadicOuterSmall_M22 : SporadicOuterSmall .M22 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m22_schreier.1 (by norm_num))

theorem sporadicOuterSmall_M23 : SporadicOuterSmall .M23 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m23_schreier.1 (by norm_num))

theorem sporadicOuterSmall_M24 : SporadicOuterSmall .M24 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_m24_schreier.1 (by norm_num))

theorem sporadicOuterSmall_J1 : SporadicOuterSmall .J1 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.at_j1_schreier.1.le (by norm_num))

theorem sporadicOuterSmall_J2 : SporadicOuterSmall .J2 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_J2_Schreier.1 (by norm_num))

theorem sporadicOuterSmall_J3 : SporadicOuterSmall .J3 :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_J3_Schreier.1 (by norm_num))

theorem sporadicOuterSmall_HS : SporadicOuterSmall .HS :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_HS_Schreier.1 (by norm_num))

theorem sporadicOuterSmall_Suz : SporadicOuterSmall .Suz :=
  Or.inl (lt_of_le_of_lt Sporadic.SuzOddCore.outer_carrier_suz.1.le (by norm_num))

theorem sporadicOuterSmall_ONan : SporadicOuterSmall .ONan :=
  Or.inr fun q hq hq5 hdvd => by
    rcases Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hdvd
      with rfl | rfl <;> omega

theorem sporadicOuterSmall_Co3 : SporadicOuterSmall .Co3 :=
  Or.inl (lt_of_le_of_lt CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le (by norm_num))

end CFSG.RankThree.PartOne
