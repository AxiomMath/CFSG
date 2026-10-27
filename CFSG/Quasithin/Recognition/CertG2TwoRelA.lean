module

public import CFSG.LieType.Ree.ConstWordCheck
public import CFSG.Quasithin.Recognition.CertG2TwoData
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem g2_rel_check_0 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 0 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_1 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 1 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_2 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 2 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_3 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 3 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_4 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 4 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_5 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 5 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_6 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 6 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_7 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 7 [])) [] = true := by
  decide +kernel

end CFSG.Quasithin
