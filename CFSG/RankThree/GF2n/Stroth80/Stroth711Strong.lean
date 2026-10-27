module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Step2
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step4
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step5
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step6
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem stroth711Strong_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement) (hNO : Sec7NOrderStatement) (hA : Sec7AExistsStatement) :
    Stroth711StrongStatement :=
  have h52c : Stroth52cStatement := stroth_5_2c h34 (stroth310NotQB_of_34 h34)
  stroth711Strong_of_n12 hA
    (n12Lemma2_of h34 h52c) (n12Lemma3_of h34 h52a h52c) (n12Lemma4_of h34)
    (n12Lemma5_of h34 hRoot) (n12WneV_of hNO h52c)

end CFSG.RankThree.GF2n.Stroth80
