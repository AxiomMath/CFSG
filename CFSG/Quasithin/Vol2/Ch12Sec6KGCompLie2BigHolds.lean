module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigAsm
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigG2
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigD4
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigF4

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint


theorem comp12626Lie2BigExc_holds : Comp12626Lie2BigExc := by
  intro Q _ K L P T v hQ h f hf hK
  have := hQ.finite
  have hA := h.autConf
  rcases hK with hK | hK | ⟨-, hK⟩ | ⟨-, hK⟩
  · exact false_of_autConf_g2 hf hK hA
  · exact false_of_autConf_3d4 hf hK hA
  · exact false_of_autConf_2f4 hK hA
  · exact false_of_autConf_sz hf hK hA

theorem comp12626Lie2Big_holds : Comp12626Lie2Big :=
  comp12626Lie2Big_of comp12626Lie2BigExc_holds

end CFSG.Quasithin.H13.S126C
