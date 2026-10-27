module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.Ch5Sec3L532Bor
import CFSG.Quasithin.Vol2.GoldschmidtF48RigL3Main

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_psl3 : ModelAt .PSL 3 := by
  intro Y _ f hpar hY
  have hm := f431ModelFacts_psl3 f
  have hfin : Finite Y := (hm Y hY).1
  refine ⟨hfin, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · obtain ⟨-, F, _, _, _, -, ⟨e⟩⟩ := L3.exists_equiv_projSL3 hY
    have := Finite.of_equiv Y e.toEquiv
    exact inf_le_normalizer_of_borelData Borel252.L3.borelData_L3 L3.no_normal_two_subgroup e
      hpair
  · exact amalgamRigid_of_f48 hm (f431Facts45_psl f hm) (f431Generation_psl3 f)
      (fun D _ hD A => Or.inl (cartanFPF_psl3 f hpar.1 hm D hD A))
      (fun D _ hD A => faithfulOnType_psl3 f hm D hD A _) Y hY hpair

theorem stmt5_3_2At_psl3 (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .PSL 3 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_psl3

end CFSG.Quasithin.H13.L532
