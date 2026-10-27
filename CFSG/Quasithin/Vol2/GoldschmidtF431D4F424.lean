module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Holds
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexXD

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.RankTwoAmalgam.Completion

section F424


@[expose] def d4Geom : D4Geom where
  e := d4E
  e_xv := d4E_xv
  e_lv := d4E_lv
  e_smul := d4E_smul
  e_adj := d4E_adj
  dist_lay := d4_dist_lay

end F424

@[expose] def D4F424 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : d4Setting.α.Completion Y), β.IsFaithful →
    Nat.card Y ≤ Nat.card d4Setting.Yb → Nat.card Y = Nat.card d4Setting.Yb ∧
      ∃ (Ġ : Type) (_ : Group Ġ), d4Setting.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ)

theorem d4F424
    (hD : IsSimpleGroup D) :
    D4F424 := fun Y _ _ β hβ hle =>
  LieSetting.lemma_F424_titsModel d4Setting (k := 4) rfl d4_titsModel d4_hpoly β hβ hle
    (fun hs => d4Geom.d4F48 hD d4_titsModel d4_hpoly Y β hβ hs)

end CFSG.Quasithin.D4Hex
