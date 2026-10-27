module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutStab
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexXD
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutAct

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F431.F45 CFSG.D4Hex

section Setting

@[expose] noncomputable def d3SettingFull : LieSetting.{0, 0} :=
  { d3Setting with N := ⊤, hN := Subgroup.normal_of_characteristic ⊤ }

end Setting

section Datum

theorem d3_smul_xv_iff (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (y : ↥(autStab d4H ⊔ autStab d4N)) :
    d3Phi y • d3Setting.ι.xv = d3Setting.ι.xv ↔ y • (Sum.inl 0 : HexVtx) = Sum.inl 0 := by
  rw [d4_smul_xv_iff, mem_range_φ1_iff_d3, d3ToAut_d3Phi, mem_autStab_H_iff hZH]
  constructor
  · intro h
    exact congrArg Sum.inl h
  · intro h
    exact Sum.inl.inj h

theorem d3_smul_lv_iff
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N)
    (y : ↥(autStab d4H ⊔ autStab d4N)) :
    d3Phi y • d3Setting.ι.lv = d3Setting.ι.lv ↔ y • (Sum.inr 0 : HexVtx) = Sum.inr 0 := by
  rw [d4_smul_lv_iff, mem_range_φ2_iff_d3, d3ToAut_d3Phi, mem_autStab_N_iff hNN]
  constructor
  · intro h
    exact congrArg Sum.inr h
  · intro h
    exact Sum.inr.inj h

theorem d3XDatum
    (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z)
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) :
    XDatum d3SettingFull d3Phi hexGraph (Sum.inl 0 : HexVtx) (Sum.inr 0 : HexVtx) where
  inj := d3Phi_injective
  N_eq := (MonoidHom.range_eq_top.2 d3Phi_surjective).symm
  dec g := by
    obtain ⟨y, rfl⟩ := d3Phi_surjective g
    exact ⟨y, 1, one_smul _ _, one_smul _ _, (mul_one _).symm⟩
  stab1 y := d3_smul_xv_iff hZH y
  stab2 y := d3_smul_lv_iff hNN y
  disj y z := Sum.inl_ne_inr
  noadj1 y z := hexGraph_not_adj_inl
  noadj2 y z := hexGraph_not_adj_inr
  adj12 := d4_adj12

end Datum

end CFSG.Quasithin.D4Hex
