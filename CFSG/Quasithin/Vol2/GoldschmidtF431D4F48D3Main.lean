module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3Holds
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Geom
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Concl

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F48Gen CFSG.D4Hex
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.Quasithin.TitsGeo (TitsModel)

@[expose] def D3F424 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : d3Setting.α.Completion Y), β.IsFaithful →
    Nat.card Y ≤ Nat.card d3Setting.Yb → Nat.card Y = Nat.card d3Setting.Yb ∧
      ∃ (Ġ : Type) (_ : Group Ġ), d3Setting.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ)

section Main

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d3_card_dvd : Nat.card d3Setting.Yb ∣ f48Order3 := by
  have hc : Nat.card D = 211341312 := card_trialityGroup8
  have h := card_d3Setting_Yb_dvd hD'
  rw [hc] at h
  exact h

include hD' in
theorem d3F48_of_geom (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) (hD : IsSimpleGroup D)
    (Gm : HexGeomOf d3Setting ↥(autStab d4H ⊔ autStab d4N) d3Phi d3Sec)
    (M : TitsModel d3Setting.ι 4) (hpoly : IsGenPolygon d3Setting.ι.graph 6)
    (Y : Type) [Group Y] [Finite Y] (β : d3Setting.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall d3Setting.m) : d3Setting.F48Concl β := by
  have hTι := Gm.toPerm_injective (d3_toPerm_injective_K3 hD)
  exact f48Concl_of_ext d3Setting (k := 4) rfl M hpoly (d3_card_dvd hD')
    (d3_ptRigid (mem_autStab_H_iff hZH) (mem_autStab_N_iff hNN) Gm) hTι
    (f48_isExtension_gen d3Setting (Gm.hfix_of fun w hw => d3_hfix_pts hw)
      (Gm.hNtr_of d3_hNtr_pts) hTι) Y β hβ hs

include hD' in
theorem d3F424_of_geom (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) (hD : IsSimpleGroup D)
    (Gm : HexGeomOf d3Setting ↥(autStab d4H ⊔ autStab d4N) d3Phi d3Sec)
    (M : TitsModel d3Setting.ι 4) (hpoly : IsGenPolygon d3Setting.ι.graph 6) : D3F424 :=
  fun Y _ _ β hβ hle =>
    LieSetting.lemma_F424_titsModel d3Setting (k := 4) rfl M hpoly β hβ hle
      (fun hs => d3F48_of_geom hD' hZH hNN hD Gm M hpoly Y β hβ hs)

theorem d3_hexGeomOf (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) :
    Nonempty (HexGeomOf d3Setting ↥(autStab d4H ⊔ autStab d4N) d3Phi d3Sec) := by
  obtain ⟨e, hxv, hlv, hsmul, hadj⟩ := d3_exists_equiv hZH hNN
  exact ⟨{
    Φ_Ψ := d3Phi_d3Sec
    hm := rfl
    e := e
    e_xv := hxv
    e_lv := hlv
    e_smul := hsmul
    e_adj := hadj
    dist_lay := d3_dist_lay }⟩

include hD' in
theorem d3F48 (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) (hD : IsSimpleGroup D)
    (Y : Type) [Group Y] [Finite Y] (β : d3Setting.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall d3Setting.m) : d3Setting.F48Concl β := by
  obtain ⟨Gm⟩ := d3_hexGeomOf hZH hNN
  exact d3F48_of_geom hD' hZH hNN hD Gm (d3_titsModel hZH hNN) (d3_hpoly hZH hNN) Y β hβ hs

include hD' in
theorem d3F424 (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) (hD : IsSimpleGroup D) :
    D3F424 := by
  obtain ⟨Gm⟩ := d3_hexGeomOf hZH hNN
  exact d3F424_of_geom hD' hZH hNN hD Gm (d3_titsModel hZH hNN) (d3_hpoly hZH hNN)

end Main

end CFSG.Quasithin.D4Hex
