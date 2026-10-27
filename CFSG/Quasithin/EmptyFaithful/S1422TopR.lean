module

public import CFSG.Quasithin.EmptyFaithful.S1422LocFinal
public import CFSG.Quasithin.Recognition.CertU33Amalgam
public import CFSG.Quasithin.Recognition.M12AmalFactsMain
public import CFSG.Quasithin.Recognition.M12AmalAutJFinal
public import CFSG.Quasithin.Recognition.M12AmalAutLFinal
public import CFSG.Quasithin.Recognition.M12AmalE8Final
public import CFSG.Quasithin.Recognition.G2AmalE8Final
public import CFSG.Quasithin.Recognition.F112RBridgesProof
public import CFSG.Quasithin.Recognition.F112TitsMain
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal
public import CFSG.Quasithin.Recognition.M12AscMain
public import CFSG.Quasithin.Recognition.ABGWreathedProof
public import CFSG.Quasithin.EmptyFaithful.S1422Facts

public section

namespace CFSG.Quasithin

theorem stageTheorem14220_of_stages_R2
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hGold : F6.GoldschmidtS3ListCat.{0}) (hHay : HayashiFiveThree)
    (hTits : TitsAmalgamLocal) (h2F4 : TwoF4AmalgamLocal) (hG2 : G2AmalgamE8)
    (hM12E8 : M12AmalgamE8) (hF431 : F431Statement) (hABG : ABGWreathedRecognition)
    (hI46 : CFSG.GH74.M12.S_Asc03_simple) : StageTheorem14220 :=
  have hF := facts1422Input_of_stages h11 h113
  stageTheorem14220_of_R hGold r2aBridges (f112R2b_of_hayashi card_Sz_zero hHay)
    (stage1422Data_of_facts1422Input hF) (stage1426VleQ_of_facts1422Input hF)
    (lemma14221Local_of_inputs (stage1426VleQ_of_facts1422Input hF) hTits h2F4 hG2 hM12E8
      autM12AmalgamLocal)
    hF431 mulAut_models_not_simple hABG g22p_amalgam_facts hI46 m12AmalgamFacts
    autM12AmalgamFacts

theorem stageTheorem14220_of_stages_R3
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hGold : F6.GoldschmidtS3ListCat.{0}) (hHay : HayashiFiveThree) (hF431 : F431Statement) :
    StageTheorem14220 :=
  stageTheorem14220_of_stages_R2 h11 h113 hGold hHay titsAmalgamLocal twoF4AmalgamLocal g2AmalgamE8
    m12AmalgamE8 hF431 abgWreathedRecognition s_Asc03_simple

end CFSG.Quasithin
