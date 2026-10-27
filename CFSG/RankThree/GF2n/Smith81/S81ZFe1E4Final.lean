module

public import CFSG.RankThree.GF2n.Smith81.S81ZFe1E4
public import CFSG.RankThree.GF2n.Smith81.S81QTorus

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.D6Spin


theorem e4TorusFacts_holds (K : Type) [Field K] [Finite K] [CharP K 2] : E4TorusFacts K :=
  ⟨isPGroup_posU0, T0_le_EAut0, fun _ ht => T0_le_normalizer_posU0 ht⟩

theorem smith24E4Uniform_of_core (hG1 : E4G1Statement)
    (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hcore : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], E4CoreStatement K) :
    Smith24E4UniformStatement :=
  smith24E4Uniform_of_inputs hG1 h34 hGen (fun K _ _ _ => e4TorusFacts_holds K) hcore

end CFSG.RankThree.GF2n.Smith81.S81Z
