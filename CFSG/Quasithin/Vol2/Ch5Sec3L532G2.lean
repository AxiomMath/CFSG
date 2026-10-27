module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Main
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_g2 :
    ModelAt .G2 0 := by
  intro Y _ f hpar hY
  have hm := G2.f431ModelFacts_g2 f
  refine ⟨(hm Y hY).1, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · exact ((Sec53F.G2.lieModelFacts_g2 Y f hpar hY).2 TY P₁ P₂ hpair).2.1
  · exact amalgamRigid_of_f48 hm (G2.f431Facts45_g2 f hm) (G2.f431Generation_g2 f)
      (fun D _ hD A => G2.F48.cartanFPF_or_swap_g2 f hm D hD A)
      (fun D _ hD A => G2.F48.faithfulOnType_g2 f hm D hD A _) Y hY hpair

theorem stmt5_3_2At_g2
    (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .G2 0 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_g2

end CFSG.Quasithin.H13.L532
