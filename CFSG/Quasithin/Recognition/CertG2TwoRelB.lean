module

public import CFSG.LieType.Ree.ConstWordCheck
public import CFSG.Quasithin.Recognition.CertG2TwoData
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem g2_rel_check_8 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 8 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_9 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 9 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_10 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 10 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_11 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 11 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_12 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 12 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_13 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 13 [])) [] = true := by
  decide +kernel

theorem g2_rel_check_14 :
    constCheck Tag.G2 2 (g2PW (u33PresRels.getD 14 [])) [] = true := by
  decide +kernel

end CFSG.Quasithin
