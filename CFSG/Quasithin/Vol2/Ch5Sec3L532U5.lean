module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rec
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_u5 :
    ModelAt .PSU 5 := by
  intro Y _ f hpar hY
  have hf : f = 2 := by
    rcases hpar.2 with h | h | h | h | h | h | h <;> first | exact h.2.2 | simp at h
  subst hf
  have hm := Un.f431ModelFacts_un5 2
  refine ⟨(hm Y hY).1, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · exact ((Sec53F.lieModelFacts_u5 Y 2 hpar hY).2 TY P₁ P₂ hpair).2.1
  · exact amalgamRigid_of_f48 hm (Un.f431Facts45_un5 2 hm) (Un.f431Generation_un5 2)
      (fun D _ hD A => Or.inl (Un.cartanFPF_un5 hm D hD A))
      (fun D _ hD A => Un.faithfulOnType_un5 2 hm D hD A _) Y hY hpair

theorem stmt5_3_2At_u5
    (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .PSU 5 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_u5

end CFSG.Quasithin.H13.L532
