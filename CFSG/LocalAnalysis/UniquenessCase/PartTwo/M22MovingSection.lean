module

public import CFSG.Quasithin.Background.M22TenNormalizerInvolutions
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CommutatorSectionFaithful

public section



namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {t : MulAut W}

theorem m22_section_mQuot_eq_three_and_not_inner
    (hW : ∀ w : W, w ^ 2 = 1) (hH : IsSpor ↥H .M22)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (commSub (⊤ : Subgroup W) H)
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 10)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (ht2 : t ^ 2 = 1)
    (htU : ∃ u ∈ commSub (⊤ : Subgroup W) H, t u ≠ u)
    (hrk : rk ↥(commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t)) ≤ 3) :
    E3.mQuot
      (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup W) H ⊓ fixV H))
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 3 ∧
    ¬ ∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹ := by
  classical
  set U : Subgroup W := commSub (⊤ : Subgroup W) H with hU
  set Z : Subgroup W := U ⊓ fixV H with hZ
  have hirr' := hirr
  rw [irrSet, Set.mem_setOf_eq] at hirr'
  obtain ⟨hcommU, hIirr⟩ := hirr'
  have hHU : H ≤ stabSub U := CFSG.Quasithin.le_stabSub_of_forall_mem hIirr.2.1
  have hne : ¬ H ≤ centSub U := by
    intro hHc
    have hUfix : U ≤ fixV H := fun u hu h hh => hHc hh u hu
    have hbot : commSub U H = ⊥ := commSub_eq_bot_iff.mpr hUfix
    rw [hcommU] at hbot
    have hlt := hIirr.1
    rw [hbot] at hlt
    simp at hlt
  obtain ⟨eH⟩ := hH
  have hsimpleCarrier : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  have hsimple : IsSimpleGroup ↥H := eH.isSimpleGroup
  have hfaith : H ⊓ centSub U = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hsimple hHU hne
  let HU : Subgroup (MulAut U) := autSub H U
  let e : ↥H ≃* ↥HU := autSubEquivOfFaithful hHU hfaith
  have hHUspor : IsSpor ↥HU .M22 := ⟨e.symm.trans eH⟩
  have htUmem : t ∈ stabSub U := by
    have h := CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer (X := H) htN
    rwa [commV_eq_commSub] at h
  let tU : MulAut U := resHom U ⟨t, htUmem⟩
  have hWU : ∀ u : U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
  have hcommHU : commSub (⊤ : Subgroup U) HU = ⊤ :=
    commSub_top_autSub_eq_top hHU hcommU
  have hdimHU : E3.mQuot (⊤ : Subgroup U) (fixV HU) = 10 := by
    have hrel := Subgroup.relIndex_map_map_of_injective (fixV HU) (⊤ : Subgroup U)
      U.subtype_injective
    rw [map_subtype_fixV_autSub hHU, Subgroup.map_top, Subgroup.range_subtype] at hrel
    unfold E3.mQuot
    rw [← hrel]
    exact hdim
  have hirrHU : commSub (⊤ : Subgroup U) HU ∈ irrSet HU :=
    mem_irrSet_autSub_of_mem_irrSet hHU hirr
  have hmap : (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)).map U.subtype =
      commSub U (Subgroup.zpowers t) := by
    simpa [tU] using CFSG.Quasithin.map_commSub_zpowers_resHom htUmem
  have hrkU : rk ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) ≤ 3 := by
    have hcard : Nat.card ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) =
        Nat.card ↥(commSub U (Subgroup.zpowers t)) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective U.subtype_injective).symm
    change padicValNat 2 (Nat.card ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU))) ≤ 3
    rw [hcard]
    exact hrk
  have htU2 : tU ^ 2 = 1 := by
    have h2 : (⟨t, htUmem⟩ : ↥(stabSub U)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using ht2
    calc tU ^ 2 = (resHom U ⟨t, htUmem⟩) ^ 2 := rfl
      _ = resHom U ((⟨t, htUmem⟩ : ↥(stabSub U)) ^ 2) := by rw [map_pow]
      _ = resHom U 1 := by rw [h2]
      _ = 1 := map_one _
  have htU1 : tU ≠ 1 := by
    obtain ⟨u, huU, htu⟩ := htU
    intro h1
    have h2 : tU ⟨u, huU⟩ = ⟨u, huU⟩ := by
      simpa using congrArg (fun f : MulAut U => f ⟨u, huU⟩) h1
    have h3 : t u = u := by
      have h4 := congrArg (fun w : U => (w : W)) h2
      simpa [tU, resHom_apply] using h4
    exact htu h3
  have htNU : tU ∈ Subgroup.normalizer (HU : Set (MulAut U)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hHmap : H.map (MulAut.conj t).toMonoidHom = H := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp htN
    have h := CFSG.Quasithin.StabLat.autSub_map_conj_eq (X := H) (U := U) htUmem
    rw [hHmap] at h
    exact h.symm
  have hB := CFSG.Quasithin.M22TenNormalizer.mQuot_commSub_sup_fixV_eq_three_and_not_inner_of_rk_le_three
    (W := U) hWU hHUspor hcommHU hirrHU hdimHU htNU htU2 htU1 hrkU
  have hq_eq : E3.mQuot (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU) (fixV HU) =
      E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z := by
    have hmapZ : (fixV HU).map U.subtype = Z := by
      rw [map_subtype_fixV_autSub hHU, hZ]
    have hmapK : (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU).map U.subtype =
        commSub U (Subgroup.zpowers t) ⊔ Z := by
      rw [Subgroup.map_sup, hmap, hmapZ]
    have hrel := Subgroup.relIndex_map_map_of_injective (fixV HU)
      (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU) U.subtype_injective
    rw [hmapZ, hmapK] at hrel
    unfold E3.mQuot
    exact congrArg (padicValNat 2) hrel.symm
  have hnotinner : ¬ ∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹ := by
    rintro ⟨h0, hh0, hconj⟩
    apply hB.2
    refine ⟨e ⟨h0, hh0⟩, (e ⟨h0, hh0⟩).2, ?_⟩
    intro k hk
    obtain ⟨h, hk_eq⟩ := e.surjective ⟨k, hk⟩
    have hkval : (↑(e h) : MulAut U) = k := by
      simpa using congrArg Subtype.val hk_eq
    rw [← hkval]
    have hmem : t * (h : MulAut W) * t⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp htN h).mp h.2
    have hmem0 : h0 * (h : MulAut W) * h0⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hh0 h.2) (H.inv_mem hh0)
    have he_conj := autSubEquivOfFaithful_map_conj hHU hfaith htUmem
      (fun l hl => (Subgroup.mem_normalizer_iff.mp htN l).mp hl) h
    have heqH : (⟨t * (h : MulAut W) * t⁻¹, hmem⟩ : ↥H) =
        ⟨h0 * (h : MulAut W) * h0⁻¹, hmem0⟩ := by
      apply Subtype.ext
      exact hconj h h.2
    have hprod : (⟨h0 * (h : MulAut W) * h0⁻¹, hmem0⟩ : ↥H) =
        ⟨h0, hh0⟩ * h * ⟨h0, hh0⟩⁻¹ := rfl
    calc tU * e h * tU⁻¹ = e ⟨t * (h : MulAut W) * t⁻¹, hmem⟩ := he_conj.symm
      _ = e ⟨h0 * (h : MulAut W) * h0⁻¹, hmem0⟩ := by rw [heqH]
      _ = e (⟨h0, hh0⟩ * h * ⟨h0, hh0⟩⁻¹) := by rw [hprod]
      _ = e ⟨h0, hh0⟩ * e h * (e ⟨h0, hh0⟩)⁻¹ := by simp [map_mul, map_inv]
  exact ⟨by rw [← hq_eq]; exact hB.1, hnotinner⟩

theorem mem_centralizer_of_m22_section_mQuot_eq_zero
    (hW : ∀ w : W, w ^ 2 = 1) (hH : IsSpor ↥H .M22)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hzero : E3.mQuot
      (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup W) H ⊓ fixV H))
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 0) :
    t ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
  have hqH : CFSG.Open.IsQuasisimple ↥H := isQuasisimple_of_isSpor_m22 hH
  obtain ⟨eH⟩ := hH
  have hsimpleCarrier : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  have hsimple : IsSimpleGroup ↥H := eH.isSimpleGroup
  exact mem_centralizer_of_commSub_sup_fixV_mQuot_eq_zero hW hsimple hqH hirr htN hzero

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
