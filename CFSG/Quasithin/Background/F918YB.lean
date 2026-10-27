module

public import CFSG.Quasithin.Background.F918YA
public import CFSG.Quasithin.Background.F918Q3
public import CFSG.Quasithin.Background.F918Q4

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

section Transport

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

private noncomputable abbrev yb_congrHom : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

private theorem yb_congrHom_apply (x : MulAut V) (v : V') :
    yb_congrHom e x v = e (x (e.symm v)) := rfl

private theorem yb_congrHom_injective : Function.Injective (yb_congrHom e) :=
  (MulAut.congr e).injective

private theorem yb_rAV_map (A : Subgroup (MulAut V)) :
    rAV (A.map (yb_congrHom e)) = rAV A :=
  CFSG.Quasithin.rAV_map_mulAutCongr e A

private theorem yb_isA2_map {X A : Subgroup (MulAut V)} (h : IsA2 X A) :
    IsA2 (X.map (yb_congrHom e)) (A.map (yb_congrHom e)) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_, ?_⟩
  · intro hb
    exact h.2.1 ((Subgroup.map_eq_bot_iff_of_injective _ (yb_congrHom_injective e)).mp hb)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.2.2.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.2.2.2 a ha, map_one]

end Transport

section Sylow

variable {W : Type} [CommGroup W]

private theorem yb_isSylowTwoOf_autSub_of_le {X T : Subgroup (MulAut W)} {U : Subgroup W}
    (hXS : X ≤ stabSub U) (hTX : T ≤ X) (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (autSub T U) (autSub X U) :=
  CFSG.Quasithin.D36.isSylowTwoOf_autSub hXS hTX hT

private theorem yb_isSylowTwoOf_autSub {X T : Subgroup (MulAut W)} {U : Subgroup W}
    (hTS : T ≤ stabSub U) (hTX : T ≤ X) (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (autSub T U) (autSub X U) := by
  have hTX' : T ≤ X ⊓ stabSub U := le_inf hTX hTS
  have h := yb_isSylowTwoOf_autSub_of_le (X := X ⊓ stabSub U) inf_le_right hTX'
    (F7.isSylowTwoOf_mono_right hT hTX' inf_le_left)
  have e : autSub (X ⊓ stabSub U) U = autSub X U := by
    unfold autSub
    rw [Subgroup.inf_subgroupOf_right]
  rwa [e] at h

end Sylow

section Restrict

variable {W : Type} [CommGroup W]

private theorem yb_autSub_conjBy {D : Subgroup (MulAut W)} {U : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub U) :
    autSub (conjBy g D) U = conjBy (resHom U ⟨g, hg⟩) (autSub D U) :=
  D36.autSub_conjBy hg

private theorem yb_exists_conj_commSub_ne_bot {T D : Subgroup (MulAut W)} {V U VT : Subgroup W}
    (hVT : VT = orbSup T V) (hVU : V ≤ U) (hnot : ¬ VT ≤ fixV D) :
    ∃ g ∈ T, commSub U (conjBy g D) ≠ ⊥ :=
  D36.exists_conj_commSub_ne_bot hVT hVU hnot

private theorem yb_autSub_le_stabSub {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hDU : D ≤ stabSub U) : autSub D VT ≤ stabSub (U.subgroupOf VT) :=
  D36.autSub_le_stabSub_subgroupOf hDU

private theorem yb_le_stabSub_of_autSub {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) (hDV : D ≤ stabSub VT) (hA : autSub D VT ≤ stabSub (U.subgroupOf VT)) :
    D ≤ stabSub U := by
  intro d hd u
  by_cases hu : u ∈ VT
  · have h := hA (mem_autSub.mpr ⟨⟨d, hDV hd⟩, hd, rfl⟩) ⟨u, hu⟩
    simpa [Subgroup.mem_subgroupOf, resHom_apply] using h
  · have h1 : d u ∉ VT := fun h' => hu ((hDV hd u).mp h')
    exact ⟨fun h' => absurd (hUV h') h1, fun h' => absurd (hUV h') hu⟩

private theorem yb_commSub_subgroupOf_ne_bot {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hDVT : D ≤ stabSub VT) (hUV : U ≤ VT) (hne : commSub U D ≠ ⊥) :
    commSub (U.subgroupOf VT) (autSub D VT) ≠ ⊥ :=
  D36.commSub_subgroupOf_autSub_ne_bot hDVT hUV hne

private theorem yb_map_autSub_autSub {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) (hDV : D ≤ stabSub VT) (hDU : D ≤ stabSub U) :
    (autSub (autSub D VT) (U.subgroupOf VT)).map
        (yb_congrHom (Subgroup.subgroupOfEquivOfLe hUV)) = autSub D U := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgY, rfl⟩ := mem_autSub.mp hψ
    obtain ⟨h, hhD, hh⟩ := mem_autSub.mp hgY
    refine mem_autSub.mpr ⟨⟨h, hDU hhD⟩, hhD, ?_⟩
    ext u
    rw [yb_congrHom_apply]
    have e1 : ((Subgroup.subgroupOfEquivOfLe hUV).symm u : ↥(U.subgroupOf VT)) =
        ⟨⟨u, hUV u.2⟩, u.2⟩ := rfl
    rw [e1]
    show ((resHom U ⟨h, hDU hhD⟩ u : ↥U) : W) =
      ((resHom (U.subgroupOf VT) g ⟨⟨u, hUV u.2⟩, u.2⟩ : ↥(U.subgroupOf VT)) : ↥VT).1
    rw [resHom_apply, resHom_apply, ← hh, resHom_apply]
  · intro hφ
    obtain ⟨d, hdD, rfl⟩ := mem_autSub.mp hφ
    have hmem : resHom VT ⟨d, hDV hdD⟩ ∈ autSub D VT :=
      mem_autSub.mpr ⟨⟨d, hDV hdD⟩, hdD, rfl⟩
    have hstab : resHom VT ⟨d, hDV hdD⟩ ∈ stabSub (U.subgroupOf VT) :=
      yb_autSub_le_stabSub hDU hmem
    refine ⟨resHom (U.subgroupOf VT) ⟨resHom VT ⟨d, hDV hdD⟩, hstab⟩,
      mem_autSub.mpr ⟨⟨resHom VT ⟨d, hDV hdD⟩, hstab⟩, hmem, rfl⟩, ?_⟩
    ext u
    rw [yb_congrHom_apply]
    have e1 : ((Subgroup.subgroupOfEquivOfLe hUV).symm u : ↥(U.subgroupOf VT)) =
        ⟨⟨u, hUV u.2⟩, u.2⟩ := rfl
    rw [e1]
    show ((resHom (U.subgroupOf VT) ⟨resHom VT ⟨d, hDV hdD⟩, hstab⟩
        ⟨⟨u, hUV u.2⟩, u.2⟩ : ↥(U.subgroupOf VT)) : ↥VT).1 = ((resHom U ⟨d, hDU hdD⟩ u : ↥U) : W)
    rw [resHom_apply, resHom_apply, resHom_apply]

private theorem yb_commSeries_autSub {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) (hDV : D ≤ stabSub VT) (hDU : D ≤ stabSub U) {k : ℕ}
    (h : commSeries (autSub D VT) k = ⊥) : commSeries (autSub D U) k = ⊥ := by
  have h1 := map_commIter_autSub hDU k
  have h2 := map_commIter_autSub hDV k
  have h3 : commIter U D k ≤ commIter VT D k := commIter_mono hUV le_rfl k
  have h4 : commIter VT D k = ⊥ := by
    rw [← h2]
    show (commSeries (autSub D VT) k).map VT.subtype = ⊥
    rw [h, Subgroup.map_bot]
  have h5 : (commSeries (autSub D U) k).map U.subtype = ⊥ := by
    show (commIter ⊤ (autSub D U) k).map U.subtype = ⊥
    rw [h1]
    exact le_bot_iff.mp (h4 ▸ h3)
  exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp h5

end Restrict

section Core

private theorem yb_exists_rat {Y : Type} [CommGroup Y] [Finite Y] {X : Subgroup (MulAut Y)}
    {k : ℕ} {c : ℚ} (h : kq X k ≤ (c : WithTop ℚ)) : ∃ r : ℚ, kq X k = (r : WithTop ℚ) ∧ r ≤ c := by
  have hne : kq X k ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  exact ⟨r, hr.symm, WithTop.coe_le_coe.mp (hr ▸ h)⟩

private theorem yb_core {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {X T : Subgroup (MulAut W)} {V VT U : Subgroup W} {U₂ : Subgroup ↥VT}
    (hVT : VT = orbSup T V) (hTS : T ≤ stabSub VT) (hTX : T ≤ X) (hSyl : IsSylowTwoOf T X)
    (hVU : V ≤ U) (hUV : U ≤ VT)
    (hP : GluedPair (autSub X VT) (U.subgroupOf VT) U₂)
    (hrank : rk ↥(U.subgroupOf VT ⊓ U₂) + 2 < rk ↥(U.subgroupOf VT))
    (hq : qOf (autSub X VT) ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ D : Subgroup (MulAut W), D ≤ T ∧ D ≤ stabSub U ∧ autSub D U ≠ ⊥ ∧
      IsElemAbelian2 (autSub D U) ∧ commSeries (autSub D U) 2 = ⊥ ∧ rAV (autSub D U) ≤ 2 := by
  have hY : ∀ y : ↥VT, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hexp y.1)
  obtain ⟨r, hr, hr2⟩ := yb_exists_rat hq
  obtain ⟨⟨A₀, hA₀, hA₀q, hA₀r⟩, -⟩ := kq_eq_coe_iff.mp hr
  have hSyl' : IsSylowTwoOf (autSub T VT) (autSub X VT) := yb_isSylowTwoOf_autSub hTS hTX hSyl
  obtain ⟨x, hx, hA₀x⟩ :=
    F7.isSylowTwoOf_exists_conj_le hSyl' hA₀.le hA₀.isElemAbelian2.isPGroup
  have hA₁ : IsA2 (autSub X VT) (conjBy x⁻¹ A₀) := hA₀.conjBy ((autSub X VT).inv_mem hx)
  have hA₁T : conjBy x⁻¹ A₀ ≤ autSub T VT := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have := hA₀x hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  obtain ⟨D₀, hD₀T, hD₀A⟩ := exists_le_of_le_autSub hA₁T
  have hnot : ¬ VT ≤ fixV D₀ := by
    intro h
    have : autSub D₀ VT = ⊥ :=
      (autSub_eq_bot_iff (hD₀T.trans hTS)).mpr (commSub_eq_bot_iff.mpr h)
    exact hA₁.ne_bot (hD₀A ▸ this)
  obtain ⟨g, hgT, hgne⟩ := yb_exists_conj_commSub_ne_bot hVT hVU hnot
  have hgS : g ∈ stabSub VT := hTS hgT
  have hDT : conjBy g D₀ ≤ T := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e]
    exact T.mul_mem (T.mul_mem hgT (hD₀T hy)) (T.inv_mem hgT)
  have hDV : conjBy g D₀ ≤ stabSub VT := hDT.trans hTS
  have hDA : autSub (conjBy g D₀) VT = conjBy (resHom VT ⟨g, hgS⟩) (conjBy x⁻¹ A₀) := by
    rw [← hD₀A]
    exact yb_autSub_conjBy hgS
  have hgX : resHom VT ⟨g, hgS⟩ ∈ autSub X VT :=
    autSub_mono hTX VT (mem_autSub.mpr ⟨⟨g, hgS⟩, hgT, rfl⟩)
  have hA2 : IsA2 (autSub X VT) (autSub (conjBy g D₀) VT) := by
    rw [hDA]
    exact hA₁.conjBy hgX
  have hAq : commSeries (autSub (conjBy g D₀) VT) 2 = ⊥ := by
    rw [hDA]
    exact (commSeries_conjBy_eq_bot_iff _ _ 2).mpr ((commSeries_conjBy_eq_bot_iff _ _ 2).mpr hA₀q)
  have hAr : rAV (autSub (conjBy g D₀) VT) = r := by
    rw [hDA, rAV_conjBy, rAV_conjBy]
    exact hA₀r
  have hAU : autSub (conjBy g D₀) VT ≤ stabSub (U.subgroupOf VT) :=
    glued_quad_offender_stab hY hP hrank hA2.le hA2.ne_bot hA2.isElemAbelian2 hAq
      (hAr.le.trans hr2)
  have hDU : conjBy g D₀ ≤ stabSub U := yb_le_stabSub_of_autSub hUV hDV hAU
  have hplus : autSub (conjBy g D₀) VT ∈ RPlus (autSub X VT) :=
    D2_3_2 hA2 hAq (by rw [hAr]; exact hr.symm)
  have h5 := D2_5 hY (X := autSub X VT) (A := autSub (conjBy g D₀) VT) (r := r)
    ⟨⟨hA2, hAr.le⟩, hplus⟩ hAU (yb_commSub_subgroupOf_ne_bot hDV hUV hgne)
  have hmap := yb_map_autSub_autSub hUV hDV hDU
  have h6 := yb_isA2_map (Subgroup.subgroupOfEquivOfLe hUV) h5.1
  rw [hmap] at h6
  refine ⟨conjBy g D₀, hDT, hDU, h6.ne_bot, h6.isElemAbelian2,
    yb_commSeries_autSub hUV hDV hDU hAq, ?_⟩
  rw [← hmap, yb_rAV_map]
  exact h5.2.trans hr2

end Core

section Plumbing

variable {W : Type} [CommGroup W]

private theorem yb_mem_stabSub_commSub {X : Subgroup (MulAut W)} {Y : Subgroup W} {g : MulAut W}
    (hgY : g ∈ stabSub Y) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    g ∈ stabSub (commSub Y X) :=
  CFSG.Quasithin.StabLat.mem_stabSub_commSub hgY hgX

private theorem yb_resHom_mem_normalizer {L : Subgroup (MulAut W)} {U : Subgroup W} {d : MulAut W}
    (hd : d ∈ stabSub U) (hdN : d ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    resHom U ⟨d, hd⟩ ∈ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) := by
  have h1 : (⟨d, hd⟩ : ↥(stabSub U)) ∈
      Subgroup.normalizer ((L.subgroupOf (stabSub U) : Subgroup ↥(stabSub U)) :
        Set ↥(stabSub U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp hdN (h : MulAut W)
  exact Subgroup.le_normalizer_map (resHom U) ⟨_, h1, rfl⟩

variable [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

private theorem yb_t_not_stab (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    t ∉ stabSub (commSub (orbSup T V) L) := by
  intro ht
  have hr := d36_rank_Y hL38 n
  rw [mem_stabSub_iff_map_eq.mp ht, inf_idem] at hr
  omega

private theorem yb_T_inf_stab_le (hL38 : D3L38) (n : D36Norm M Mp T L V t) {s : MulAut W}
    (hsT : s ∈ T) (hs : s ∈ stabSub (commSub (orbSup T V) L)) :
    s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rcases d36_split hL38 n s hsT with h | h
  · exact h
  · exfalso
    apply yb_t_not_stab hL38 n
    have hr : t⁻¹ * s ∈ stabSub (commSub (orbSup T V) L) :=
      yb_mem_stabSub_commSub (le_stabSub_orbSup T V (T.mul_mem (T.inv_mem n.tT) hsT)) h
    have h' := (stabSub (commSub (orbSup T V) L)).mul_mem hs
      ((stabSub (commSub (orbSup T V) L)).inv_mem hr)
    rwa [show s * (t⁻¹ * s)⁻¹ = t by group] at h'

end Plumbing

theorem d36_quad_offender_restrict {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ D : Subgroup (MulAut W), D ≤ T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ∧
      autSub D (commSub (orbSup T V) L) ≠ ⊥ ∧
      IsElemAbelian2 (autSub D (commSub (orbSup T V) L)) ∧
      commSeries (autSub D (commSub (orbSup T V) L)) 2 = ⊥ ∧
      rAV (autSub D (commSub (orbSup T V) L)) ≤ 2 ∧
      autSub D (commSub (orbSup T V) L) ≤
        Subgroup.normalizer (autSub L (commSub (orbSup T V) L) :
          Set (MulAut ↥(commSub (orbSup T V) L))) := by
  have hD := n.std.hyp
  have hMpM : Mp ≤ M := by
    rw [hD.Mp_eq]
    exact conjClosure_le fun s hs z hz =>
      M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hz)) (M.inv_mem (hD.sylow.1 hs))
  have hSyl : IsSylowTwoOf T (Mp ⊔ T) :=
    F7.isSylowTwoOf_mono_right hD.sylow le_sup_right (sup_le hMpM hD.sylow.1)
  have hUV : commSub (orbSup T V) L ≤ orbSup T V :=
    le_sup_left.trans (d36_orbSup_eq_sup hL38 n).le
  have hP : GluedPair (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
    ⟨d36_sup_Y hL38 n, d36_perm_Y hL38 n, d36_swap_Y hL38 n, d36_faithful_Y hL38 n⟩
  obtain ⟨D, hDT, hDU, h1, h2, h3, h4⟩ := yb_core hD.exp rfl (le_stabSub_orbSup T V) le_sup_right
    hSyl (d36_V_le_U hL38 n) hUV hP (d36_rank_Y hL38 n) hq
  have hDN : D ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun d hd =>
    yb_T_inf_stab_le hL38 n (hDT hd) (hDU hd)
  refine ⟨D, le_inf hDT hDN, h1, h2, h3, h4, ?_⟩
  intro φ hφ
  obtain ⟨⟨d, hd⟩, hdD, rfl⟩ := mem_autSub.mp hφ
  exact yb_resHom_mem_normalizer hd (hDN hdD)

end CFSG.Quasithin
