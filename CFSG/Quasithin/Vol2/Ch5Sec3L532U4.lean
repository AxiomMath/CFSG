module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.GoldschmidtF431UnGlue
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU4

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_u4 :
    ModelAt .PSU 4 := by
  intro Y _ f hpar hY
  have hm := Un.f431ModelFacts_un f
  refine ⟨(hm Y hY).1, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · exact ((Sec53F.lieModelFacts_u4 Y f hpar hY).2 TY P₁ P₂ hpair).2.1
  · exact amalgamRigid_of_f48 hm (Un.f431Facts45_un f hm) (Un.f431Generation_un f)
      (fun D _ hD A => Or.inl (Un.cartanFPF_un f hpar.1 hm D hD A))
      (fun D _ hD A => Un.faithfulOnType_un f hm D hD A _) Y hY hpair

theorem stmt5_3_2At_u4
    (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .PSU 4 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_u4

end CFSG.Quasithin.H13.L532
