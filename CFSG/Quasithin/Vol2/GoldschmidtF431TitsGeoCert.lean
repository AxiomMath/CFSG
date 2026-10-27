module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoModel

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin

theorem titsModel :
    TitsModel titsSetting.ι 6 ∧ IsGenPolygon titsSetting.ι.graph 8 :=
  titsModel_of_check Certificates.certificate4190

theorem lemma_F424_tits
    {Y : Type} [Group Y] [Finite Y]
    (β : titsSetting.α.Completion Y) (hβ : β.IsFaithful)
    (hle : Nat.card Y ≤ Nat.card titsSetting.Yb)
    (h48 : β.IsSmall titsSetting.m → titsSetting.F48Concl β) :
    Nat.card Y = Nat.card titsSetting.Yb ∧
      ∃ (Ġ : Type) (_ : Group Ġ), titsSetting.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ) :=
  LieSetting.lemma_F424_titsModel titsSetting (k := 6) rfl titsModel.1 titsModel.2 β hβ hle h48

end CFSG.Quasithin.TitsGeo
