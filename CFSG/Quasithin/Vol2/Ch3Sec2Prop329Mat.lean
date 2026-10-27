module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Rows
public import CFSG.Quasithin.Vol2.Ch10SecQ1M2x
public import CFSG.Quasithin.Background.SmithB45MatQ
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.H13.Prop329.Mat

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
  CFSG.Quasithin.Vol2.Ch10.SecA

theorem nonempty_stab_two_equiv
    {x y : Fin 24} (hxy : x ≠ y) :
    Nonempty (↥(AutPerm ⊓ stab x ⊓ stab y) ≃* NativeSporadic.M22) := by
  obtain ⟨τ, hτ, h0, h1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  have hmap := C10P01.map_conj_stab01 hτ
  rw [h0, h1] at hmap
  exact ⟨(((AutPerm ⊓ stab 0 ⊓ stab 1).equivMapOfInjective _ (MulAut.conj τ).injective).trans
    (MulEquiv.subgroupCongr hmap)).symm.trans mog22EquivM22⟩

theorem nonempty_stab_equiv
    (x : Fin 24) :
    Nonempty (↥(AutPerm ⊓ stab x) ≃* NativeSporadic.M23) := by
  obtain ⟨v, hv⟩ := exists_ne x
  obtain ⟨τ, hτ, h0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x v hv.symm
  have hmap := C10P01.map_conj_stab0 hτ
  rw [h0] at hmap
  exact ⟨(((AutPerm ⊓ stab 0).equivMapOfInjective _ (MulAut.conj τ).injective).trans
    (MulEquiv.subgroupCongr hmap)).symm.trans mog23EquivM23⟩

theorem nonempty_autPerm_equiv :
    Nonempty (↥AutPerm ≃* NativeSporadic.M24) := by
  obtain ⟨h1, h2, -⟩ := mog_catalog_M24_bridge
  exact ⟨(MulEquiv.subgroupCongr (h1.trans h2)).trans
    (NativeSporadic.M24.equivMapOfInjective _ (MulAut.conj bridgeQ⁻¹).injective).symm⟩

end CFSG.Quasithin.H13.Prop329.Mat

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
  CFSG.Quasithin.Vol2.Ch10.SecA Prop329 Prop329.Mat

theorem row329M22_holds :
    Row329M22 := by
  intro V _ _ G L hHyp h
  have hnt := nontrivial_of_b4Hyp hHyp
  have hLG : IsOver L G := ⟨(FFC.b4hyp_data hHyp).1, B42L2.le_normalizer_of_b4Hyp hHyp⟩
  refine ⟨?_, (stmtH13Card V L).2.2 (Or.comm.mp h), fun hc => B45Mat.two_lt_qOf_cocode22 hLG hc⟩
  rcases h with ⟨x, y, hxy, hr⟩ | ⟨x, y, hxy, hr⟩
  · obtain ⟨hs, -⟩ := C10P01.stab_props_m22 hxy
    obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple hs hnt hr
    obtain ⟨e₂⟩ := nonempty_stab_two_equiv hxy
    exact ⟨e₁.trans e₂⟩
  · obtain ⟨hs, -⟩ := C10P01.stab_props_m22 hxy
    obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple hs hnt hr
    obtain ⟨e₂⟩ := nonempty_stab_two_equiv hxy
    exact ⟨e₁.trans e₂⟩

theorem row329M23_holds :
    Row329M23 := by
  intro V _ _ G L hHyp h
  have hnt := nontrivial_of_b4Hyp hHyp
  refine ⟨?_, (stmtH13Card V L).2.1 (Or.comm.mp h)⟩
  rcases h with ⟨x, hr⟩ | ⟨x, hr⟩
  · obtain ⟨hs, -⟩ := C10P01.stab_props_m23 x
    obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple hs hnt hr
    obtain ⟨e₂⟩ := nonempty_stab_equiv x
    exact ⟨e₁.trans e₂⟩
  · obtain ⟨hs, -⟩ := C10P01.stab_props_m23 x
    obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple hs hnt hr
    obtain ⟨e₂⟩ := nonempty_stab_equiv x
    exact ⟨e₁.trans e₂⟩

theorem row329M24_holds : Row329M24 := by
  intro V _ _ G L hHyp h
  have hnt := nontrivial_of_b4Hyp hHyp
  refine ⟨?_, (stmtH13Card V L).1 (Or.comm.mp h)⟩
  obtain ⟨e₂⟩ := nonempty_autPerm_equiv
  rcases h with hr | hr
  · obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple AutPerm_isSimpleGroup hnt hr
    exact ⟨e₁.trans e₂⟩
  · obtain ⟨e₁⟩ := nonempty_mulEquiv_of_simple AutPerm_isSimpleGroup hnt hr
    exact ⟨e₁.trans e₂⟩

theorem row329HatM22_holds : Row329HatM22 := by
  intro V _ _ L h
  obtain ⟨K, _, _, Γ₀, hK, hhat, -, π, hπ⟩ := h
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ₀) hπ
  have e : ↥L ≃* ↥Γ₀ := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  obtain ⟨hperf, hZ, hquot⟩ := isHat_parts_of_mulEquiv e hhat
  refine ⟨hperf, hZ, hquot, ?_⟩
  have hcard := card_eq_of_realizesVia_nat hπ
  rw [Subgroup.card_top, Subgroup.card_bot, mul_one, Nat.card_fun, hK] at hcard
  rw [hcard]
  norm_num

end CFSG.Quasithin.H13
