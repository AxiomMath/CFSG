module

public import CFSG.LieType.Ree.ConstWordCheck
public import CFSG.Quasithin.Recognition.CertG2TwoData
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem g2_invol_check_0 :
    constCheck Tag.G2 2 (g2W (g2LetterStr 0) ++ g2W (g2LetterStr 0)) [] = true := by
  decide +kernel

theorem g2_invol_check_1 :
    constCheck Tag.G2 2 (g2W (g2LetterStr 1) ++ g2W (g2LetterStr 1)) [] = true := by
  decide +kernel

theorem g2_invol_check_2 :
    constCheck Tag.G2 2 (g2W (g2LetterStr 2) ++ g2W (g2LetterStr 2)) [] = true := by
  decide +kernel

theorem g2_invol_check_3 :
    constCheck Tag.G2 2 (g2W (g2LetterStr 3) ++ g2W (g2LetterStr 3)) [] = true := by
  decide +kernel

theorem g2_comm_check_0 :
    constCheck Tag.G2 2 (g2GenWord 0)
      (g2Comm (g2W (g2CommG.getD 0 "")) (g2W (g2CommH.getD 0 ""))) = true := by
  decide +kernel

theorem g2_comm_check_1 :
    constCheck Tag.G2 2 (g2GenWord 1)
      (g2Comm (g2W (g2CommG.getD 1 "")) (g2W (g2CommH.getD 1 ""))) = true := by
  decide +kernel

theorem g2_comm_check_2 :
    constCheck Tag.G2 2 (g2GenWord 2)
      (g2Comm (g2W (g2CommG.getD 2 "")) (g2W (g2CommH.getD 2 ""))) = true := by
  decide +kernel

theorem g2_comm_check_3 :
    constCheck Tag.G2 2 (g2GenWord 3)
      (g2Comm (g2W (g2CommG.getD 3 "")) (g2W (g2CommH.getD 3 ""))) = true := by
  decide +kernel

theorem g2_comm_check_4 :
    constCheck Tag.G2 2 (g2GenWord 4)
      (g2Comm (g2W (g2CommG.getD 4 "")) (g2W (g2CommH.getD 4 ""))) = true := by
  decide +kernel

theorem g2_cword_check :
    constCheck Tag.G2 2 (g2W (g2LetterStr 2)) (g2PW (u33Word g2CPres)) = true := by
  decide +kernel

theorem g2_conjb_check_0 :
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord 0 ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + 0) ""))) = true := by
  decide +kernel

theorem g2_conjb_check_1 :
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord 1 ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + 1) ""))) = true := by
  decide +kernel

theorem g2_conjb_check_2 :
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord 2 ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + 2) ""))) = true := by
  decide +kernel

theorem g2_conjb_check_3 :
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord 3 ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + 3) ""))) = true := by
  decide +kernel

theorem g2_conjb_check_4 :
    constCheck Tag.G2 2
      (g2W (g2LetterStr 1) ++ g2GenWord 4 ++ g2Inv (g2W (g2LetterStr 1)))
      (g2PW (u33Word (g2ConjStrings.getD (5 * 1 + 4) ""))) = true := by
  decide +kernel

end CFSG.Quasithin
