module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporM
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporJ1
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporJ2HS
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporHeRu
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporJ4
public import CFSG.Quasithin.Vol2.Ch10SecA312AG
public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp

public section

namespace CFSG.Quasithin.H13.S126C

theorem comp12626Sporadic_holds :
    Comp12626Sporadic := by
  intro Q _ K L P T v hQ h s hs ⟨e⟩
  have hS := CFSG.Quasithin.Vol2.Ch10.A312A.sporadicAutInner_proved
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.not_m11 hQ hS e
  · exact h.not_m12 hQ hS e
  · exact h.not_m22 hQ hS e
  · exact h.not_m23 hQ hS e
  · exact h.not_m24 hQ hS e
  · exact h.not_j1 hQ e
  · exact h.not_j2 hQ hS e
  · exact h.not_j4 hQ hS e
  · exact h.not_hs hQ hS e
  · exact h.not_he hQ hS e
  · exact h.not_ru hQ hS e

end CFSG.Quasithin.H13.S126C
