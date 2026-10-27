module

public import CFSG.Quasithin.H13.OverSylowHeOuter
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzHeCore

public section

namespace CFSG.Quasithin.H13.LocDbl.OverHe

open CFSG.Sporadic.He (J heEquivJ)

theorem heAutInner_kz2_holds :
    CFSG.Quasithin.H13.HeAutInner_kz2 := by
  intro Q _ _ hQe S B _ hSc hSB hBc _ f hf hfB
  obtain ⟨e⟩ := hQe
  have e' : Q ≃* CFSG.Blueprint.NativeSporadic.He := e
  have hHe := AutInner.transport' (Q := CFSG.Blueprint.NativeSporadic.He) (J := J) heAutInner_J heEquivJ
  exact AutInner.transport_hom (Q := Q) (J := CFSG.Blueprint.NativeSporadic.He) hHe e' S B hSc hSB hBc f hf hfB

end CFSG.Quasithin.H13.LocDbl.OverHe
