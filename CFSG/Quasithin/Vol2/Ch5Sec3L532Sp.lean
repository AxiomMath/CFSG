module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.Ch5Sec3L532Bor
import CFSG.Quasithin.Vol2.GoldschmidtF48RigSpMain

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_psp : ModelAt .PSp 2 := by
  intro Y _ f hpar hY
  have hm := f431ModelFacts_psp f
  have hfin : Finite Y := (hm Y hY).1
  refine ⟨hfin, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ := exists_equiv_antiSp hY
    have := Finite.of_equiv Y e.toEquiv
    exact inf_le_normalizer_of_borelData (SpModel.borel_antiSp hf hF) (SpModel.O2_antiSp hf hF) e
      hpair
  · exact amalgamRigid_of_f48 hm (f431Facts45_psp f hm) (f431Generation_psp f)
      (fun D _ hD A => Or.inl (cartanFPF_psp f hpar.1 hm D hD A))
      (fun D _ hD A => faithfulOnType_psp f hm D hD A _) Y hY hpair

theorem stmt5_3_2At_psp (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .PSp 2 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_psp

end CFSG.Quasithin.H13.L532
