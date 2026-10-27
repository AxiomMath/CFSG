module

public import CFSG.Quasithin.Background.F918J3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.IrrSetQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
public import CFSG.Quasithin.EmptyFaithful.SzF53MNat

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem autSubEquivOfFaithful_map_conj {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSub U = ⊥) {t : MulAut W}
    (htU : t ∈ stabSub U) (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (l : ↥L) :
    autSubEquivOfFaithful hLU hfaith
        ⟨t * (l : MulAut W) * t⁻¹, htL l l.2⟩ =
      resHom U ⟨t, htU⟩ * autSubEquivOfFaithful hLU hfaith l *
        (resHom U ⟨t, htU⟩)⁻¹ := by
  have hg_apply : ∀ (x : ↥L) (v : U),
      (((autSubEquivOfFaithful hLU hfaith x : ↥(autSub L U)) : MulAut U) v : W) =
        (x : MulAut W) (v : W) := by
    intro x v
    rw [autSubEquivOfFaithful_apply]
    rfl
  have hres_inv : ∀ v : U,
      (↑(((resHom U ⟨t, htU⟩ : MulAut U))⁻¹ v) : W) = t⁻¹ (v : W) := by
    intro v
    rw [← map_inv (resHom U) ⟨t, htU⟩]
    rfl
  ext u
  calc
    (((autSubEquivOfFaithful hLU hfaith
        ⟨t * (l : MulAut W) * t⁻¹, htL l l.2⟩ : ↥(autSub L U)) : MulAut U) u : W)
        = (⟨t * (l : MulAut W) * t⁻¹, htL l l.2⟩ : ↥L).1 (u : W) := hg_apply _ u
    _ = (t * (l : MulAut W) * t⁻¹) (u : W) := rfl
    _ = t ((l : MulAut W) (t⁻¹ (u : W))) := by simp [MulAut.mul_apply]
    _ = t ((l : MulAut W) ((((resHom U ⟨t, htU⟩ : MulAut U))⁻¹ u : U) : W)) := by
          rw [hres_inv]
    _ = t ((((autSubEquivOfFaithful hLU hfaith l : ↥(autSub L U)) : MulAut U)
          ((((resHom U ⟨t, htU⟩ : MulAut U))⁻¹ u)) : U) : W) := by
          rw [hg_apply]
    _ = ((((resHom U ⟨t, htU⟩ : MulAut U) *
            ((autSubEquivOfFaithful hLU hfaith l : ↥(autSub L U)) : MulAut U) *
            ((resHom U ⟨t, htU⟩ : MulAut U))⁻¹) u : U) : W) := by
          simp [MulAut.mul_apply, resHom_apply]

theorem autSub_zpowers_eq_zpowers_resHom {U : Subgroup W} {t : MulAut W}
    (htU : t ∈ stabSub U) :
    autSub (Subgroup.zpowers t) U = Subgroup.zpowers (resHom U ⟨t, htU⟩) := by
  show ((Subgroup.zpowers t).subgroupOf (stabSub U)).map (resHom U) =
    Subgroup.zpowers (resHom U ⟨t, htU⟩)
  exact CFSG.Quasithin.F53Mod.map_zpowers_subgroupOf (resHom U) htU

theorem map_commSub_zpowers_resHom {U : Subgroup W} {t : MulAut W}
    (htU : t ∈ stabSub U) :
    (commSub (⊤ : Subgroup U) (Subgroup.zpowers (resHom U ⟨t, htU⟩))).map U.subtype =
      commSub U (Subgroup.zpowers t) := by
  have h := CFSG.Quasithin.FFC.map_commSub_autSub (V₂ := U) (G₂ := Subgroup.zpowers t)
    (Subgroup.zpowers_le.mpr htU) (⊤ : Subgroup U)
  rwa [autSub_zpowers_eq_zpowers_resHom htU, Subgroup.map_top, Subgroup.range_subtype] at h

end CFSG.Quasithin

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem isIrrOn_top_fixV_autSub_of_isIrrOn {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hXU : X ≤ stabSub U) (hI : IsIrrOn (W := W) X U (U ⊓ fixV X)) :
    IsIrrOn (W := U) (autSub X U) ⊤ (fixV (autSub X U)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_lt_map_iff_of_injective U.subtype_injective).mp (by
      rw [map_subtype_fixV_autSub hXU, Subgroup.map_top, Subgroup.range_subtype]
      exact hI.1)
  · intro x _ u _
    exact Subgroup.mem_top _
  · intro x hx u hu
    rw [mem_fixV] at hu ⊢
    intro y hy
    rw [hu x hx, hu y hy]
  · intro J hJstab hNJ _
    let J' : Subgroup W := J.map U.subtype
    have hJ'stab : StableUnder X J' := by
      intro x hx w hw
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hw
      have hx' : resHom U ⟨x, hXU hx⟩ ∈ autSub X U :=
        mem_autSub.mpr ⟨⟨x, hXU hx⟩, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨resHom U ⟨x, hXU hx⟩ j, hJstab _ hx' j hj, rfl⟩
    have hNJ' : U ⊓ fixV X ≤ J' := by
      have h1 : (fixV (autSub X U)).map U.subtype ≤ J' := Subgroup.map_mono hNJ
      rwa [map_subtype_fixV_autSub hXU] at h1
    have hJ'U : J' ≤ U := by
      rintro _ ⟨j, -, rfl⟩
      exact j.2
    rcases hI.2.2.2 J' hJ'stab hNJ' hJ'U with h | h
    · left
      have hmap : (fixV (autSub X U)).map U.subtype = J' := by
        rw [map_subtype_fixV_autSub hXU, h]
      exact (Subgroup.map_injective U.subtype_injective hmap).symm
    · right
      have hmap : (⊤ : Subgroup U).map U.subtype = J' := by
        rw [Subgroup.map_top, Subgroup.range_subtype, h]
      exact (Subgroup.map_injective U.subtype_injective hmap).symm

theorem mem_irrSet_autSub_of_mem_irrSet {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hXU : X ≤ stabSub U) (hirr : U ∈ irrSet (W := W) X) :
    commSub (⊤ : Subgroup U) (autSub X U) ∈ irrSet (W := U) (autSub X U) := by
  have h : commSub U X = U ∧ IsIrrOn (W := W) X U (U ⊓ fixV X) := by
    simpa only [irrSet, Set.mem_setOf_eq] using hirr
  have hcomm := commSub_top_autSub_eq_top (W := W) hXU h.1
  rw [irrSet, Set.mem_setOf_eq, hcomm, top_inf_eq]
  exact ⟨hcomm, isIrrOn_top_fixV_autSub_of_isIrrOn (W := W) hXU h.2⟩

variable [Finite W] {H : Subgroup (MulAut W)} {t : MulAut W}

theorem mem_centralizer_of_commSub_sup_fixV_mQuot_eq_zero
    (hW : ∀ w : W, w ^ 2 = 1)
    (hHsimple : IsSimpleGroup ↥H)
    (hHq : CFSG.Open.IsQuasisimple ↥H)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hzero : E3.mQuot
      (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup W) H ⊓ fixV H))
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 0) :
    t ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
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
  have hfaith : H ⊓ centSub U = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hHsimple hHU hne
  let HU : Subgroup (MulAut U) := autSub H U
  let e : ↥H ≃* ↥HU := autSubEquivOfFaithful hHU hfaith
  have htUmem : t ∈ stabSub U := by
    have h := CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer (X := H) htN
    rwa [commV_eq_commSub] at h
  let tU : MulAut U := resHom U ⟨t, htUmem⟩
  have hWU : ∀ u : U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
  have hV2 : IsPGroup 2 ↥(commSub U (Subgroup.zpowers t) ⊔ Z) := fun y =>
    ⟨1, Subtype.ext (by simpa using hW (y : W))⟩
  have hEq : Z = commSub U (Subgroup.zpowers t) ⊔ Z :=
    (E3.mQuot_eq_zero_iff hV2 le_sup_right).mp hzero
  have hZle : commSub U (Subgroup.zpowers t) ≤ Z := by
    rw [hEq]
    exact le_sup_left
  have htU_triv : ∀ u : U, tU u * u⁻¹ ∈ fixV HU := by
    intro u
    have hgen : t (u : W) * (u : W)⁻¹ ∈ commSub U (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, u.2, rfl⟩
    have hgenW : ((tU u * u⁻¹ : U) : W) ∈ commSub U (Subgroup.zpowers t) := by
      simpa [tU, resHom_apply] using hgen
    have hgenZ : ((tU u * u⁻¹ : U) : W) ∈ Z := hZle hgenW
    rw [hZ] at hgenZ
    have hgenmap : ((tU u * u⁻¹ : U) : W) ∈ (fixV HU).map U.subtype := by
      rw [map_subtype_fixV_autSub hHU]
      exact hgenZ
    obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hgenmap
    have hzu : z = tU u * u⁻¹ := Subtype.ext hzv
    rwa [hzu] at hz
  have hcommHU : commSub (⊤ : Subgroup U) HU = ⊤ :=
    commSub_top_autSub_eq_top hHU hcommU
  have hqHU : CFSG.Open.IsQuasisimple ↥HU :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hHq
  obtain ⟨Q, hQc, hQf, qU, ρU, hqsurj, hqker, hρinj, heq, -, -, -⟩ :=
    s16k_qm_quotMap (W := U) (H := HU) hqHU hcommHU hWU
  letI : CommGroup Q := hQc
  letI : Finite Q := hQf
  have htU_trivQ : ∀ u : U, qU (tU u) = qU u := by
    intro u
    have h1 : qU (tU u * u⁻¹) = 1 := (hqker (tU u * u⁻¹)).mpr (htU_triv u)
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have htU_norm : tU ∈ Subgroup.normalizer (HU : Set (MulAut U)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hHmap : H.map (MulAut.conj t).toMonoidHom = H := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp htN
    have h := CFSG.Quasithin.StabLat.autSub_map_conj_eq (X := H) (U := U) htUmem
    rw [hHmap] at h
    exact h.symm
  have hcentral : ∀ k : ↥HU, tU * k * tU⁻¹ = k := by
    intro k
    have hc_mem : tU * k * tU⁻¹ ∈ HU := (Subgroup.mem_normalizer_iff.mp htU_norm k).mp k.2
    have hc1_mem : tU * k * tU⁻¹ * k⁻¹ ∈ HU := HU.mul_mem hc_mem (HU.inv_mem k.2)
    have hρ_conj : ρU ⟨tU * k * tU⁻¹, hc_mem⟩ = ρU k := by
      ext q
      obtain ⟨u, rfl⟩ := hqsurj q
      have hinv : qU (tU⁻¹ u) = qU u := by
        have h := htU_trivQ (tU⁻¹ u)
        rw [MulAut.apply_inv_self] at h
        exact h.symm
      calc ρU ⟨tU * k * tU⁻¹, hc_mem⟩ (qU u)
          = qU ((tU * k * tU⁻¹) u) := (heq ⟨tU * k * tU⁻¹, hc_mem⟩ u).symm
        _ = qU (tU ((k : MulAut U) (tU⁻¹ u))) := by simp [MulAut.mul_apply]
        _ = qU ((k : MulAut U) (tU⁻¹ u)) := htU_trivQ _
        _ = ρU k (qU (tU⁻¹ u)) := heq k (tU⁻¹ u)
        _ = ρU k (qU u) := by rw [hinv]
    have hρ_one : ρU ⟨tU * k * tU⁻¹ * k⁻¹, hc1_mem⟩ = 1 := by
      rw [show (⟨tU * k * tU⁻¹ * k⁻¹, hc1_mem⟩ : ↥HU) =
          ⟨tU * k * tU⁻¹, hc_mem⟩ * k⁻¹ from rfl,
        map_mul, map_inv, hρ_conj, mul_inv_cancel]
    have hk1 : (⟨tU * k * tU⁻¹ * k⁻¹, hc1_mem⟩ : ↥HU) = 1 :=
      hρinj (by rw [hρ_one, map_one])
    exact mul_inv_eq_one.mp (congrArg Subtype.val hk1)
  have hconjH : ∀ h ∈ H, t * h * t⁻¹ = h := by
    intro h hh
    let hH : ↥H := ⟨h, hh⟩
    have hmem : t * h * t⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp htN h).mp hh
    have he_conj' : e ⟨t * (hH : MulAut W) * t⁻¹, hmem⟩ = tU * e hH * tU⁻¹ := by
      simpa using autSubEquivOfFaithful_map_conj hHU hfaith htUmem
        (fun l hl => (Subgroup.mem_normalizer_iff.mp htN l).mp hl) hH
    have h1 : e ⟨t * h * t⁻¹, hmem⟩ = e hH := by
      apply Subtype.ext
      rw [show (⟨t * h * t⁻¹, hmem⟩ : ↥H) = ⟨t * (hH : MulAut W) * t⁻¹, hmem⟩ from rfl]
      rw [he_conj']
      exact hcentral (e hH)
    exact congrArg Subtype.val (e.injective h1)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 := hconjH h hh
  calc h * t = (t * h * t⁻¹) * t := by rw [h1]
    _ = t * h := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
