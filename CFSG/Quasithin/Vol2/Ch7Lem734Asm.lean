module

public import CFSG.Quasithin.Vol2.Ch7Lem734Main
public import CFSG.Quasithin.Vol2.Ch7Lem734A6
public import CFSG.Quasithin.Vol2.Ch7Lem734S7
public import CFSG.Quasithin.Vol2.Ch7Lem734Wr
public import CFSG.Quasithin.Vol2.Ch7Lem734L3Wr
public import CFSG.Quasithin.Vol2.Ch7Lem734SL3Pair
public import CFSG.Quasithin.Vol2.Ch7Lem734SL3PairM
public import CFSG.Quasithin.Vol2.Ch7Lem734Sp4Pair
public import CFSG.Quasithin.Vol2.Ch7Lem734SU3
public import CFSG.Quasithin.Vol2.Ch7Lem734L3Nine
public import CFSG.Quasithin.Vol2.Ch7Lem734Sz
public import CFSG.Quasithin.Vol2.Ch7Lem734MathieuM
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch3Sec2Wreath
public import CFSG.Quasithin.Vol2.Ch7Lem734MathieuN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.QuasithinUnique

theorem stmt7_3_4_E336_wreath_of_lemmas (h4414 : Stmt4_4_14) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) : Stmt7_3_4_E336_wreath := by
  intro G _ _ T L I hyp _ _ _ _ hrow
  obtain ⟨hIV, hTI⟩ := isTISetUnder_fsuV_of_row711L3Wreath hyp.fsu hrow
  exact ⟨hTI, local_structure_wreath h4414 hC58 h317 h37 h38 h39 h3228 hyp hrow hIV hTI⟩

theorem stmt7_3_4_of_rows
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (h4414 : Stmt4_4_14)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h325 : Stmt3_2_5)
    (h63 : ASInputs.AS_E_6_3) (hin : Input8_1_2) (h711 : Stmt7_1_1)
    (h711n : Stmt7_1_1_normal) (h771 : Stmt7_7_1) : Stmt7_3_4 :=
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat
    (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  stmt7_3_4_of hE22 h331 h4414 hC58 h317 h37 h38 h39 h3228 h325 h63 hin h711 h711n h771
    (stmt7_3_4_E336_wreath_of_lemmas h4414 hC58 h317 h37 h38 h39 h3228)
    stmt7_2_1_Sp4Pair stmt7_2_1_S7 stmt7_3_4_nPrime_SU3 stmt7_3_4_nPrime_Sz
    stmt7_3_4_nPrime_L3Nine stmt7_3_4_nPrime_Mathieu stmt7_3_4_nPrime_SL3Pair
    stmt7_3_4_nPrime_SL3One stmt7_3_4_nPrime_Sp4Pair stmt7_3_4_nPrime_A6Pair stmt7_3_4_nPrime_S7Pair
    stmt7_3_4_nPrime_L3Wreath stmt7_2_1_m_Sz stmt7_2_1_m_L3Nine stmt7_2_1_m_Mathieu
    stmt7_2_1_m_SL3Pair stmt7_2_1_m_L3Wreath

end CFSG.Quasithin.H13
