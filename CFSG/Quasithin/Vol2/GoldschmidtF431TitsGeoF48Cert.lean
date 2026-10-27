module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Holds
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoCert

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin

theorem titsF48
    (Y : Type) [Group Y] [Finite Y]
    (β : titsSetting.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall titsSetting.m) :
    titsSetting.F48Concl β :=
  titsF48_of_check Certificates.certificate4190 Certificates.certificate4191 Y β hβ hs

theorem hF424
    (Y : Type) [Group Y] [Finite Y]
    (β : titsSetting.α.Completion Y) (hβ : β.IsFaithful)
    (hle : Nat.card Y ≤ Nat.card titsSetting.Yb) :
    Nat.card Y = Nat.card titsSetting.Yb ∧
      ∃ (Ġ : Type) (_ : Group Ġ), titsSetting.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ) :=
  lemma_F424_tits β hβ hle (titsF48 Y β hβ)

end CFSG.Quasithin.TitsGeo
