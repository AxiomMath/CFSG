module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Main
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Main

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_d4 :
    ModelAt .trialityD4 0 := by
  intro Y _ f hpar hY
  have hm := D4q.Hex.f431ModelFacts_d4 f
  refine ⟨(hm Y hY).1, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · exact ((Sec53F.lieModelFacts_d4 Y f hpar hY).2 TY P₁ P₂ hpair).2.1
  · exact amalgamRigid_of_f48 hm (D4q.Hex.f431Facts45_d4 f hm) (D4q.Hex.f431Generation_d4 f)
      (fun D _ hD A => Or.inl (D4q.F48.cartanFPF_d4 f hpar.1 hm D hD A))
      (fun D _ hD A => D4q.F48.faithfulOnType_d4 f hpar.1 hm D hD A _) Y hY hpair

theorem stmt5_3_2At_d4
    (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .trialityD4 0 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_d4

end CFSG.Quasithin.H13.L532
