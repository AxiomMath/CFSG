module

public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.RankThree.PartOne.S11c.Sec66E6
public import CFSG.RankThree.PartOne.S11c.Sec66E6Tw
public import CFSG.RankThree.PartOne.S11c.Sec66E78
public import CFSG.RankThree.PartOne.S11c.Sec66F4
public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub
public import CFSG.RankThree.PartOne.S11c.Sec66Orth
public import CFSG.RankThree.PartOne.S11c.Sec66PSL2
public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.RankThree.PartOne.S11c.Sec66Sp4
public import CFSG.RankThree.PartOne.S11c.Sec66SpK2
public import CFSG.RankThree.PartOne.S11c.Sec66Sz
public import CFSG.RankThree.PartOne.S11c.Sec66Tits

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)

theorem sec66T_K1_twistedF4_final :
    Sec66T_K1 .twistedF4 :=
  sec66T_K1_twistedF4 CFSG.RankThree.PartOne.RF4.largeReeFieldAutCoset

theorem sec66T_K1_twistedG2 : Sec66T_K1 .twistedG2 := by
  intro T _ _ p hp hp5 hmodel
  obtain ⟨n, f, hadm, -⟩ := hmodel
  exact absurd hadm.2.2.2.1 (by norm_num)

theorem sec66T_K2_twistedG2 : Sec66T_K2 .twistedG2 := by
  intro T _ _ p hp hp5 hmodel
  obtain ⟨n, f, hadm, -⟩ := hmodel
  exact absurd hadm.2.2.2.1 (by norm_num)

theorem sec66T_K1_all :
    ∀ t, Sec66T_K1 t := by
  intro t
  cases t
  · exact sec66T_K1_PSL psl_two_k1 psl_torus_rank
  · exact sec66T_K1_PSU
  · exact sec66T_K1_PSp sp4SubfieldCaseExcluded
  · exact sec66T_K1_POmegaOdd
  · exact sec66T_K1_POmegaPlus
  · exact sec66T_K1_POmegaMinus
  · exact sec66T_K1_G2 g2SubfieldCaseExcluded
  · exact sec66T_K1_F4
  · exact sec66T_K1_E6
  · exact sec66T_K1_E78 .E7 .E7 rfl (Or.inl rfl) fun hf => admissible_E7 hf
  · exact sec66T_K1_E78 .E8 .E8 rfl (Or.inr rfl) fun hf => admissible_E8 hf
  · exact sec66T_K1_twistedE6
  · exact sec66T_K1_trialityD4
  · exact sec66T_K1_Sz
  · exact sec66T_K1_twistedG2
  · exact sec66T_K1_twistedF4_final
  · exact sec66T_K1_Tits

theorem sec66T_K2_all :
    ∀ t, Sec66T_K2 t := by
  intro t
  cases t
  · exact sec66T_K2_PSL psl_torus_rank
  · exact sec66T_K2_PSU
  · exact sec66T_K2_PSp
  · exact sec66T_K2_POmegaOdd
  · exact sec66T_K2_POmegaPlus
  · exact sec66T_K2_POmegaMinus
  · exact sec66T_K2_G2
  · exact sec66T_K2_F4
  · exact sec66T_K2_E6
  · exact sec66T_K2_E78 .E7 .E7 rfl (Or.inl rfl)
  · exact sec66T_K2_E78 .E8 .E8 rfl (Or.inr rfl)
  · exact sec66T_K2_twistedE6
  · exact sec66T_K2_trialityD4
  · exact sec66T_K2_Sz
  · exact sec66T_K2_twistedG2
  · exact sec66T_K2_twistedF4
  · exact sec66T_K2_Tits

end CFSG.RankThree.PartOne.Sec66T
