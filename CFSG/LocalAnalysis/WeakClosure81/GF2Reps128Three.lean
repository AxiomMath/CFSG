module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Orbit
public import CFSG.Quasithin.Vol2.Ch10SecC8H1A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W]

theorem autQuot_zpowers {C : Subgroup W} {t : MulAut W} (htC : t ∈ stabSub C) :
    autQuot (Subgroup.zpowers t) C = Subgroup.zpowers (quotHom C ⟨t, htC⟩) := by
  ext φ
  rw [mem_autQuot]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgk : g = (⟨t, htC⟩ : stabSub C) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hgk, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  · intro hφ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    refine ⟨(⟨t, htC⟩ : stabSub C) ^ k, ?_, map_zpow _ _ _⟩
    rw [Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers _ k

variable [Finite W]

theorem rkIdx_fixV_eq_rk_commSub {H : Subgroup (MulAut W)} (htop : (⨆ I ∈ irrSet H, I) = ⊤)
    {C U : Subgroup W} (hU0 : U ⊓ C = ⊥) {s : MulAut W} (hsC : s ∈ stabSub C)
    (hUs : U.map s.toMonoidHom = U) (hs : ∀ I ∈ irrSet H, I ≠ U → ∀ w ∈ I, s w = w) :
    rkIdx (fixV (Subgroup.zpowers s)) =
      rk ↥(commSub (U.map (QuotientGroup.mk' C)) (Subgroup.zpowers (quotHom C ⟨s, hsC⟩))) := by
  have hsU : s ∈ stabSub U := mem_stabSub_of_forall_mem fun u hu => by
    rw [← hUs]
    exact ⟨u, hu, rfl⟩
  have hzU : ∀ x ∈ Subgroup.zpowers s, ∀ u ∈ U, x u ∈ U := fun x hx u hu =>
    (((Subgroup.zpowers_le.mpr hsU) hx) u).mpr hu
  have hcomm : commV (Subgroup.zpowers s) = commSub U (Subgroup.zpowers s) := by
    apply le_antisymm
    · rw [commV_eq_commSub, ← htop, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [iSup_subtype'] at hw
      refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
        (C := fun w => (s ^ k) w * w⁻¹ ∈ commSub U (Subgroup.zpowers s)) hw ?_ ?_ ?_
      · intro I w hw
        by_cases hIU : (I : Subgroup W) = U
        · exact Subgroup.subset_closure ⟨s ^ k, Subgroup.zpow_mem_zpowers _ k, w, hIU ▸ hw, rfl⟩
        · rw [zpow_apply_eq_self (hs I I.2 hIU w hw) k, mul_inv_cancel]
          exact Subgroup.one_mem _
      · simp
      · intro a b ha hb
        have he : (s ^ k) (a * b) * (a * b)⁻¹ = ((s ^ k) a * a⁻¹) * ((s ^ k) b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [he]
        exact Subgroup.mul_mem _ ha hb
    · rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
  have h1 := rk_commV_add_rk_fixV s
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s))
  have h3 := rk_map_mk (commSub U (Subgroup.zpowers s)) C
  have hinf : commSub U (Subgroup.zpowers s) ⊓ C = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right C (commSub_le_of_invariant hzU)).trans hU0.le)
  rw [hinf, rk_bot, add_zero] at h3
  have h4 : (commSub U (Subgroup.zpowers s)).map (QuotientGroup.mk' C) =
      commSub (U.map (QuotientGroup.mk' C)) (Subgroup.zpowers (quotHom C ⟨s, hsC⟩)) := by
    rw [← autQuot_zpowers hsC,
      commSub_map_mk (Subgroup.zpowers_le.mpr hsC) U]
  rw [hcomm] at h1
  rw [h4] at h3
  omega

omit [Finite W] in
theorem eq_of_forall_mem_irrSet {H : Subgroup (MulAut W)} (htop : (⨆ I ∈ irrSet H, I) = ⊤)
    {g h : MulAut W} (hgh : ∀ I ∈ irrSet H, ∀ w ∈ I, g w = h w) : g = h := by
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ ⨆ I ∈ irrSet H, I := by rw [htop]; trivial
  rw [iSup_subtype'] at hw
  refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
    (C := fun w => g w = h w) hw ?_ ?_ ?_
  · intro I w hw
    exact hgh I I.2 w hw
  · simp
  · intro a b ha hb
    rw [map_mul, map_mul, ha, hb]

theorem commV_eq_of_le_centSub {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (htop : (⨆ I ∈ irrSet H, I) = ⊤) {U : Subgroup W}
    (hU : U ∈ irrSet H) (hLU : ¬ commSub U L ≤ fixV H) {R : Subgroup (MulAut W)} (hLR : L ≤ R)
    (hRU : R ≤ stabSub U) (hRtriv : ∀ I ∈ irrSet H, I ≠ U → R ≤ centSub I) : commV R = U := by
  apply le_antisymm
  · rw [commV_eq_commSub, ← htop, commSub, Subgroup.closure_le]
    rintro _ ⟨r, hr, w, hw, rfl⟩
    rw [iSup_subtype'] at hw
    refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
      (C := fun w => r w * w⁻¹ ∈ U) hw ?_ ?_ ?_
    · intro I w hw
      by_cases hIU : (I : Subgroup W) = U
      · have hwU : w ∈ U := hIU ▸ hw
        exact U.mul_mem (((hRU hr) w).mpr hwU) (U.inv_mem hwU)
      · rw [hRtriv I I.2 hIU hr w hw, mul_inv_cancel]
        exact U.one_mem
    · simp
    · intro a b ha hb
      have he : r (a * b) * (a * b)⁻¹ = (r a * a⁻¹) * (r b * b⁻¹) := by
        rw [map_mul, mul_inv, mul_mul_mul_comm]
      rw [he]
      exact U.mul_mem ha hb
  · calc U = commSub U L := (commSub_eq_self_of_not_le hL hH hU (self_mem_conjSet L Y) hLU).symm
      _ ≤ commV R := by
        rw [commV_eq_commSub]
        exact commSub_mono le_top hLR

theorem isSubnormal_sup_zpowers {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : t * t = 1) (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) :
    IsSubnormal L (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) := by
  have hLtcomp : IsComponentOf (L.map (MulAut.conj t).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hL ht
  have hc := B69.components_mul_comm_of_ne hL hLtcomp (Ne.symm hmove)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set B := L ⊔ L.map (MulAut.conj t).toMonoidHom with hB
  have h1 : (L.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun k hk => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [hc k hk l hl, mul_inv_cancel_right]
      exact hl
    · intro hl
      have hx := hc k⁻¹ ((L.map (MulAut.conj t).toMonoidHom).inv_mem hk) _ hl
      have h2 : l = k * l * k⁻¹ := by
        calc l = k⁻¹ * (k * l * k⁻¹) * k := by group
          _ = (k * l * k⁻¹) * k⁻¹ * k := by rw [hx]
          _ = k * l * k⁻¹ := by group
      rw [h2]
      exact hl
  have hconj : ∀ h ∈ B, t * h * t⁻¹ ∈ B := by
    have hle : B.map (MulAut.conj t).toMonoidHom ≤ B := by
      rw [hB, Subgroup.map_sup]
      refine sup_le le_sup_right ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine (le_sup_left : L ≤ _) ?_
      have e : (MulAut.conj t).toMonoidHom ((MulAut.conj t).toMonoidHom x) = x := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [ht2, one_mul, mul_one]
      rw [e]
      exact hx
    intro h hh
    exact hle ⟨h, hh, rfl⟩
  have h2 : (B.subgroupOf (B ⊔ Subgroup.zpowers t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj h, fun hh => ?_⟩
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      rw [htinv]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2, one_mul, mul_one]
    rw [← e]
    exact hconj _ hh
  exact IsSubnormal.step le_sup_left h1 (IsSubnormal.step le_sup_left h2 (IsSubnormal.refl _))

section Moves

variable (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
  (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (ht : t ∈ Y)
  (ht2 : orderOf t = 2) (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
  (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
  (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) {U : Subgroup W} (hU : U ∈ irrSet H)
  (hLU : ¬ commSub U L ≤ fixV H)
include hD hW hL hH ht ht2 hfix hm hmove hU hLU

theorem le_centSub_of_moves (hC0 : fixV H = ⊥) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hIU : I ≠ U) :
    L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t ≤ centSub I := by
  have hcent : ∀ {X : Subgroup (MulAut W)}, commSub I X ≤ fixV H → X ≤ centSub I := by
    intro X h x hx w hw
    have h2 := h (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
    rw [hC0, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  obtain ⟨hl1, hl2⟩ := commSub_le_of_ne hD hW hL hH ht ht2 hfix hm hmove hU hLU hI hIU
  exact sup_le (sup_le (hcent hl1) (hcent hl2))
    (hcent (commSub_zpowers_le_of_ne hD hW hL hH ht ht2 hfix hm hmove hU hLU hI hIU))

theorem map_conj_eq_of_moves (hC0 : fixV H = ⊥) (hU0 : U ⊓ fixV H = ⊥)
    (htop : (⨆ I ∈ irrSet H, I) = ⊤) {e : ℕ}
    (hunU : ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H →
      X = L ∨ X = L.map (MulAut.conj t).toMonoidHom)
    (htrk : rkIdx (fixV (Subgroup.zpowers t)) = e)
    (hsw : ∀ s : ↥(secStab (fixV H) (U.map (QuotientGroup.mk' (fixV H)))), s * s = 1 →
      L.map (MulAut.conj ((s : stabSub (fixV H)) : MulAut W)).toMonoidHom =
        L.map (MulAut.conj t).toMonoidHom →
      rkIdx (fixV (Subgroup.zpowers (secHom (fixV H) (U.map (QuotientGroup.mk' (fixV H))) s))) =
        e →
      secHom (fixV H) (U.map (QuotientGroup.mk' (fixV H))) s ∈
        autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) (fixV H))
          (U.map (QuotientGroup.mk' (fixV H))))
    {g : MulAut W} (hg : g ∈ Y) (hUg : U.map g.toMonoidHom = U) :
    (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t).map
        (MulAut.conj g).toMonoidHom = L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t := by
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hUt := hfix U hU
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨-, hLtH, -⟩ := conjSet_facts hL hH hLt
  have hLtU := not_commSub_map_conj_le hL hH ht hfix hU hLU
  have hRtriv := fun I (hI : I ∈ irrSet H) (hIU : I ≠ U) =>
    le_centSub_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hC0 hI hIU
  have hHU : H ≤ stabSub U := B1.le_stabSub_of_invariant hU.2.2.1
  have htU' : t ∈ stabSub U := CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hUt
  have hRU : L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t ≤ stabSub U :=
    sup_le (sup_le (hLH.trans hHU) (hLtH.trans hHU)) (Subgroup.zpowers_le.mpr htU')
  have hpair : ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H →
      X ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom := by
    intro X hX hXU
    rcases hunU X hX hXU with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  set C := fixV H with hC
  have hgU : g ∈ stabSub U := CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hUg
  have hUg' : U.map g⁻¹.toMonoidHom = U :=
    CFSG.Quasithin.map_eq_of_mem_stabSub ((stabSub U).inv_mem hgU)
  have hLg := not_commSub_le_map_conj hL hH hg hLU
  rw [hUg] at hLg
  have hLtg := not_commSub_le_map_conj hL hH hg hLtU
  rw [hUg] at hLtg
  have hLgc : L.map (MulAut.conj g).toMonoidHom ∈ conjSet L Y := ⟨g, hg, rfl⟩
  have hLtgc : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom ∈
      conjSet L Y := ⟨g * t, Y.mul_mem hg ht, CFSG.Quasithin.B19.map_conj_map_conj L g t⟩
  set s := g * t * g⁻¹ with hs
  have hsY : s ∈ Y := Y.mul_mem (Y.mul_mem hg ht) (Y.inv_mem hg)
  have hsC : s ∈ stabSub C := hstab hsY
  have hsU : s ∈ stabSub U :=
    (stabSub U).mul_mem ((stabSub U).mul_mem hgU htU') ((stabSub U).inv_mem hgU)
  have hUs : U.map s.toMonoidHom = U := CFSG.Quasithin.map_eq_of_mem_stabSub hsU
  have hs2 : s * s = 1 := by
    calc s * s = g * (t * t) * g⁻¹ := by rw [hs]; group
      _ = 1 := by rw [ht2', mul_one, mul_inv_cancel]
  have hsoth : ∀ I ∈ irrSet H, I ≠ U → ∀ w ∈ I, s w = w := by
    intro I hI hIU w hw
    have hJ : I.map g⁻¹.toMonoidHom ∈ irrSet H :=
      map_mem_irrSet (hn g⁻¹ (Y.inv_mem hg)) (by simpa using hn g hg) hI
    have hJU : I.map g⁻¹.toMonoidHom ≠ U := by
      intro h
      apply hIU
      rw [← hUg, ← h, Subgroup.map_map]
      ext x
      simp
    have h1 : t (g⁻¹ w) = g⁻¹ w :=
      hRtriv _ hJ hJU ((le_sup_right : _ ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ _)
        (Subgroup.mem_zpowers t)) (g⁻¹ w) ⟨w, hw, rfl⟩
    rw [hs, MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.apply_inv_self]
  have hLs : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
    have hLgi := not_commSub_le_map_conj hL hH (Y.inv_mem hg) hLU
    rw [hUg'] at hLgi
    have hLgic : L.map (MulAut.conj g⁻¹).toMonoidHom ∈ conjSet L Y := ⟨g⁻¹, Y.inv_mem hg, rfl⟩
    have hLsc : L.map (MulAut.conj s).toMonoidHom ∈ conjSet L Y := ⟨s, hsY, rfl⟩
    have hLsU := not_commSub_le_map_conj hL hH hsY hLU
    rw [hUs] at hLsU
    rcases hunU _ hLsc hLsU with h | h
    · exfalso
      have h2 : (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom =
          L.map (MulAut.conj g⁻¹).toMonoidHom := by
        have h3 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
        rw [CFSG.Quasithin.B19.map_conj_map_conj] at h3
        rw [CFSG.Quasithin.B19.map_conj_map_conj]
        rwa [show g⁻¹ * s = t * g⁻¹ by rw [hs]; group] at h3
      rcases hunU _ hLgic hLgi with h4 | h4
      · rw [h4] at h2
        exact hmove h2
      · rw [h4, map_conj_map_conj_of_mul_eq_one L ht2'] at h2
        exact hmove h2.symm
    · exact h
  have hrks : rkIdx (fixV (Subgroup.zpowers s)) = e := by
    rw [← htrk, hs, CFSG.Quasithin.fixV_zpowers_conj]
    unfold rkIdx
    rw [Subgroup.index_map_of_bijective g.bijective]
  have hsS : (⟨s, hsC⟩ : stabSub C) ∈ secStab C (U.map (QuotientGroup.mk' C)) :=
    mem_secStab_of_map_eq hsC hUs
  have hz : autSub (autQuot (Subgroup.zpowers s) C) (U.map (QuotientGroup.mk' C)) =
      Subgroup.zpowers (secHom C (U.map (QuotientGroup.mk' C)) ⟨⟨s, hsC⟩, hsS⟩) :=
    autSub_autQuot_zpowers ⟨⟨s, hsC⟩, hsS⟩
  have hrkfix : rkIdx (fixV (Subgroup.zpowers s)) =
      rkIdx (fixV (autSub (autQuot (Subgroup.zpowers s) C) (U.map (QuotientGroup.mk' C)))) := by
    rw [rkIdx_fixV_eq_rk_commSub htop hU0 hsC hUs hsoth, rk_commSub_eq_rkIdx_autSub hsC hUs]
  have hmem := hsw ⟨⟨s, hsC⟩, hsS⟩ (Subtype.ext (Subtype.ext hs2)) hLs (by
    rw [← hz, ← hrkfix]
    exact hrks)
  obtain ⟨r₀, hr₀R, hr₀⟩ := mem_autSub_autQuot.mp hmem
  have hrs : ((r₀ : stabSub C) : MulAut W) = s := by
    refine eq_of_forall_mem_irrSet htop fun I hI w hw => ?_
    by_cases hIU : I = U
    · rw [hIU] at hw
      have h2 := congrArg (fun φ : MulAut ↥(U.map (QuotientGroup.mk' C)) =>
        ((φ ⟨_, w, hw, rfl⟩ : ↥(U.map (QuotientGroup.mk' C))) : W ⧸ C)) hr₀
      simp only [secHom_apply, QuotientGroup.mk'_apply, quotHom_mk] at h2
      have h3 := (mk_eq_mk_iff _ _).mp h2
      have h4 : ((r₀ : stabSub C) : MulAut W) w * (s w)⁻¹ ∈ U ⊓ C :=
        ⟨U.mul_mem (((hRU hr₀R) w).mpr hw) (U.inv_mem ((hsU w).mpr hw)), h3⟩
      rw [hU0, Subgroup.mem_bot, mul_inv_eq_one] at h4
      exact h4
    · rw [hRtriv I hI hIU hr₀R w hw, hsoth I hI hIU w hw]
  have hsR : s ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t := hrs ▸ hr₀R
  have hle : (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t).map
      (MulAut.conj g).toMonoidHom ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (sup_le ((hpair _ hLgc hLg).trans le_sup_left)
      ((hpair _ hLtgc hLtg).trans le_sup_left)) ?_
    rw [Subgroup.zpowers_le]
    exact hsR
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem isDirSumOver_of_moves (hC0 : fixV H = ⊥) (htop : (⨆ I ∈ irrSet H, I) = ⊤)
    (hunU : ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H →
      X = L ∨ X = L.map (MulAut.conj t).toMonoidHom)
    (hnormU : ∀ g ∈ Y, U.map g.toMonoidHom = U →
      (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t).map
        (MulAut.conj g).toMonoidHom = L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) :
    IsDirSumOver (conjSet (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) Y)
      commV := by
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hUt := hfix U hU
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨-, hLtH, -⟩ := conjSet_facts hL hH hLt
  have hHU : H ≤ stabSub U := B1.le_stabSub_of_invariant hU.2.2.1
  have hRU : L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t ≤ stabSub U :=
    sup_le (sup_le (hLH.trans hHU) (hLtH.trans hHU))
      (Subgroup.zpowers_le.mpr (CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hUt))
  have hcommR := commV_eq_of_le_centSub hL hH htop hU hLU (le_sup_left.trans le_sup_left) hRU
    fun I hI hIU => le_centSub_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hC0 hI hIU
  set R := L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t with hR
  have hcent : ∀ {I : Subgroup W} {X : Subgroup (MulAut W)}, commSub I X ≤ fixV H →
      ∀ x ∈ X, ∀ w ∈ I, x w = w := by
    intro I X h x hx w hw
    have h2 := h (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
    rw [hC0, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hnorm' : ∀ g ∈ Y, ∀ x ∈ H, g⁻¹ * x * g ∈ H := fun g hg x hx => by
    simpa using hn g⁻¹ (Y.inv_mem hg) x hx
  have hcommX : ∀ g : MulAut W, commV (R.map (MulAut.conj g).toMonoidHom) =
      U.map g.toMonoidHom := fun g => by rw [CFSG.Quasithin.commV_map_conj_eq, hcommR]
  refine ⟨fun X₀ => ?_, ?_⟩
  · obtain ⟨g₀, hg₀, hX₀⟩ := X₀.2
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
    have hv1' : v ∈ commV (X₀ : Subgroup (MulAut W)) := hv1
    rw [hX₀, hcommX g₀] at hv1'
    have hfixK : ∀ K ∈ conjSet L Y, ∀ k ∈ K, k v = v := by
      intro K hK k hk
      have hK' : K.map (MulAut.conj g₀⁻¹).toMonoidHom ∈ conjSet L Y := by
        obtain ⟨n, hn', rfl⟩ := hK
        exact ⟨g₀⁻¹ * n, Y.mul_mem (Y.inv_mem hg₀) hn', CFSG.Quasithin.B19.map_conj_map_conj L _ _⟩
      have hKback : (K.map (MulAut.conj g₀⁻¹).toMonoidHom).map (MulAut.conj g₀).toMonoidHom =
          K := by
        rw [CFSG.Quasithin.B19.map_conj_map_conj, mul_inv_cancel,
          CFSG.Quasithin.Asc81c.Pf.map_conj_one]
      by_cases hK'U : commSub U (K.map (MulAut.conj g₀⁻¹).toMonoidHom) ≤ fixV H
      ·
        have hKU : commSub (U.map g₀.toMonoidHom) K ≤ fixV H := by
          rw [← hKback, commSub_map_conj, ← map_fixV_of_normalizes (hn g₀ hg₀) (hnorm' g₀ hg₀)]
          exact Subgroup.map_mono hK'U
        exact hcent hKU k hk v hv1'
      ·
        have hfixX : ∀ X : ↥(conjSet R Y), X ≠ X₀ →
            ∀ w ∈ commV (X : Subgroup (MulAut W)), k w = w := by
          intro X hX w hw
          obtain ⟨g, hg, hXg⟩ := X.2
          rw [hXg, hcommX g] at hw
          refine hcent ?_ k hk w hw
          by_contra hKg
          apply hX
          have hUgirr : U.map g.toMonoidHom ∈ irrSet H :=
            map_mem_irrSet (hn g hg) (hnorm' g hg) hU
          have hJ : (U.map g.toMonoidHom).map g₀⁻¹.toMonoidHom ∈ irrSet H :=
            map_mem_irrSet (hn g₀⁻¹ (Y.inv_mem hg₀)) (by simpa using hn g₀ hg₀) hUgirr
          have h5 := not_commSub_le_map_conj hL hH (Y.inv_mem hg₀) hKg
          have hLJ : ¬ commSub ((U.map g.toMonoidHom).map g₀⁻¹.toMonoidHom) L ≤ fixV H := by
            rcases hunU _ hK' hK'U with h7 | h7
            · rwa [h7] at h5
            · rw [h7] at h5
              have h8 := not_commSub_le_map_conj hL hH ht h5
              rwa [hfix _ hJ, map_conj_map_conj_of_mul_eq_one L ht2'] at h8
          have hJU := eq_of_not_commSub_le hD hW hL hH ht ht2 hfix hm hmove hU hLU hJ hLJ
          have hgg : U.map (g₀⁻¹ * g).toMonoidHom = U := by
            have e : (g₀⁻¹ * g).toMonoidHom = g₀⁻¹.toMonoidHom.comp g.toMonoidHom := by
              ext x
              simp [MulAut.mul_apply]
            rw [e, ← Subgroup.map_map, hJU]
          have hR' := hnormU _ (Y.mul_mem (Y.inv_mem hg₀) hg) hgg
          apply Subtype.ext
          rw [hXg, hX₀]
          calc R.map (MulAut.conj g).toMonoidHom
              = (R.map (MulAut.conj (g₀⁻¹ * g)).toMonoidHom).map (MulAut.conj g₀).toMonoidHom := by
                rw [CFSG.Quasithin.B19.map_conj_map_conj, mul_inv_cancel_left]
            _ = R.map (MulAut.conj g₀).toMonoidHom := by rw [hR']
        have hv2' : v ∈ ⨆ (X : ↥(conjSet R Y)) (_ : X ≠ X₀), commV (X : Subgroup (MulAut W)) :=
          hv2
        rw [iSup_subtype'] at hv2'
        refine Subgroup.iSup_induction
          (fun X : {X : ↥(conjSet R Y) // X ≠ X₀} =>
            commV ((X : ↥(conjSet R Y)) : Subgroup (MulAut W)))
          (C := fun w => k w = w) hv2' ?_ ?_ ?_
        · intro X w hw
          exact hfixX X.1 X.2 w hw
        · exact map_one k
        · intro a b ha hb
          rw [map_mul, ha, hb]
    have hvH : v ∈ fixV H := by
      intro h hh
      rw [hH, iSup_subtype'] at hh
      refine Subgroup.iSup_induction (fun K : conjSet L Y => (K : Subgroup (MulAut W)))
        (C := fun h => h v = v) hh ?_ ?_ ?_
      · intro K k hk
        exact hfixK K K.2 k hk
      · rfl
      · intro a b ha hb
        rw [MulAut.mul_apply, hb, ha]
    rw [hC0, Subgroup.mem_bot] at hvH
    rw [Subgroup.mem_bot]
    exact hvH
  ·
    rw [eq_top_iff, ← htop]
    refine iSup₂_le fun I hI => ?_
    obtain ⟨g, hg, rfl⟩ := exists_eq_map_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hI
    have hX : R.map (MulAut.conj g).toMonoidHom ∈ conjSet R Y := ⟨g, hg, rfl⟩
    rw [← hcommX g]
    exact le_iSup (fun X : ↥(conjSet R Y) => commV (X : Subgroup (MulAut W))) ⟨_, hX⟩

theorem isNaturalO4Plus_of_moves (hC0 : fixV H = ⊥) (hU0 : U ⊓ fixV H = ⊥)
    (htop : (⨆ I ∈ irrSet H, I) = ⊤) {e : ℕ}
    (hnat : IsNaturalO4Plus (autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔
      Subgroup.zpowers t) (fixV H)) (U.map (QuotientGroup.mk' (fixV H)))) e) :
    IsNaturalO4Plus (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) e := by
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have hUt := hfix U hU
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨-, hLtH, -⟩ := conjSet_facts hL hH hLt
  have hHU : H ≤ stabSub U := B1.le_stabSub_of_invariant hU.2.2.1
  have hRtriv := fun I (hI : I ∈ irrSet H) (hIU : I ≠ U) =>
    le_centSub_of_moves hD hW hL hH ht ht2 hfix hm hmove hU hLU hC0 hI hIU
  set R := L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t with hR
  have hRY : R ≤ Y := sup_le (sup_le hL.1 (hLtH.trans hHY)) (Subgroup.zpowers_le.mpr ht)
  have hRC : R ≤ stabSub (fixV H) := hRY.trans hstab
  have hRU : R ≤ stabSub U := sup_le (sup_le (hLH.trans hHU) (hLtH.trans hHU))
    (Subgroup.zpowers_le.mpr (CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hUt))
  have hcommR : commV R = U :=
    commV_eq_of_le_centSub hL hH htop hU hLU (le_sup_left.trans le_sup_left) hRU hRtriv
  have hfaith : ∀ r ∈ R, (∀ u ∈ U, r u = u) → r = 1 := fun r hr hrU =>
    eq_of_forall_mem_irrSet htop fun I hI w hw => by
      by_cases hIU : I = U
      · rw [hIU] at hw
        exact hrU w hw
      · exact hRtriv I hI hIU hr w hw
  have hRS : ∀ r (hr : r ∈ R), (⟨r, hRC hr⟩ : stabSub (fixV H)) ∈
      secStab (fixV H) (U.map (QuotientGroup.mk' (fixV H))) := fun r hr =>
    mem_secStab_of_map_eq (hRC hr) (CFSG.Quasithin.map_eq_of_mem_stabSub (hRU hr))
  have hinj : Function.Injective (secRes hRC hRS) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨r, hr⟩ h1
    refine Subtype.ext (hfaith r hr fun u hu => ?_)
    have h2 := congrArg (fun φ : ↥(autSub (autQuot R (fixV H)) (U.map (QuotientGroup.mk' (fixV H)))) =>
      (((φ : MulAut ↥(U.map (QuotientGroup.mk' (fixV H)))) ⟨_, u, hu, rfl⟩ :
        ↥(U.map (QuotientGroup.mk' (fixV H)))) : W ⧸ fixV H)) h1
    simp only [secRes_apply, OneMemClass.coe_one, MulAut.one_apply, QuotientGroup.mk'_apply,
      quotHom_mk] at h2
    have h3 := (mk_eq_mk_iff _ _).mp h2
    have h4 : r u * u⁻¹ ∈ U ⊓ fixV H := ⟨U.mul_mem (((hRU hr) u).mpr hu) (U.inv_mem hu), h3⟩
    rw [hU0, Subgroup.mem_bot, mul_inv_eq_one] at h4
    exact h4
  set φ := MulEquiv.ofBijective (secRes hRC hRS) ⟨hinj, secRes_surjective hRC hRS⟩ with hφ
  have hmkinj : Function.Injective ((QuotientGroup.mk' (fixV H)).subgroupMap U) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ h1
    have h2 : QuotientGroup.mk' (fixV H) u = 1 := congrArg Subtype.val h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : u ∈ U ⊓ fixV H := ⟨hu, h2⟩
    rw [hU0, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  set μ := MulEquiv.ofBijective ((QuotientGroup.mk' (fixV H)).subgroupMap U)
    ⟨hmkinj, (QuotientGroup.mk' (fixV H)).subgroupMap_surjective U⟩ with hμ
  have hRstab : autQuot R (fixV H) ≤ stabSub (U.map (QuotientGroup.mk' (fixV H))) :=
    (autQuot_le_iff hRC).mpr fun r hr => mem_liftSub.mpr ⟨hRC hr, hRS r hr⟩
  have hcommUR : commSub U R = U :=
    le_antisymm (commSub_le_of_invariant fun r hr u hu => ((hRU hr) u).mpr hu)
      ((commSub_eq_self_of_not_le hL hH hU (self_mem_conjSet L Y) hLU).symm.le.trans
        (commSub_mono le_rfl (le_sup_left.trans le_sup_left)))
  have hcomm₁ : commV (autSub (autQuot R (fixV H)) (U.map (QuotientGroup.mk' (fixV H)))) = ⊤ := by
    have h1 := commSub_eq_map_commV hRstab
    rw [commSub_map_mk hRC U, hcommUR] at h1
    rw [eq_top_iff]
    intro v _
    have hv : (v : W ⧸ fixV H) ∈
        (commV (autSub (autQuot R (fixV H)) (U.map (QuotientGroup.mk' (fixV H))))).map
          (U.map (QuotientGroup.mk' (fixV H))).subtype := by
      rw [← h1]
      exact v.2
    obtain ⟨v', hv', hv'v⟩ := hv
    rwa [← Subtype.ext hv'v]
  let f : ↥(commV R) ≃*
      ↥(commV (autSub (autQuot R (fixV H)) (U.map (QuotientGroup.mk' (fixV H))))) :=
    ((MulEquiv.subgroupCongr hcommR).trans μ).trans
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcomm₁.symm))
  have hf : ∀ w : ↥(commV R), (((f w : ↥(commV (autSub (autQuot R (fixV H))
      (U.map (QuotientGroup.mk' (fixV H)))))) : ↥(U.map (QuotientGroup.mk' (fixV H)))) :
        W ⧸ fixV H) = QuotientGroup.mk' (fixV H) (w : W) := fun w => rfl
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := hnat
  refine ⟨K, hKf, hKfin, hKc, φ.symm.toMonoidHom.comp π, ?_⟩
  refine CFSG.Quasithin.Vol2.Ch10.SecC.realizesVia_transport hπ φ.symm f.symm ?_ bot_le ?_ ?_ ?_
  · intro u
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : f.symm u = 1 := Subtype.ext h
      have h2 := congrArg f h1
      rw [MulEquiv.apply_symm_apply, map_one] at h2
      exact congrArg Subtype.val h2
    · intro h
      have h1 : u = 1 := Subtype.ext h
      rw [h1, map_one]
      rfl
  · intro h' u hu
    rw [hcommR] at hu ⊢
    exact ((hRU h'.2) u).mpr hu
  · intro h' z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro g u hu
    obtain ⟨r, rfl⟩ := φ.surjective g
    rw [MulEquiv.symm_apply_apply]
    have hwU : ((f.symm u : ↥(commV R)) : W) ∈ U := hcommR.le (f.symm u).2
    have hrw : (r : MulAut W) ((f.symm u : ↥(commV R)) : W) ∈ commV R :=
      hcommR.ge (((hRU r.2) _).mpr hwU)
    have key : f ⟨_, hrw⟩ = ⟨_, hu⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hf]
      have hu' : ((u : ↥(U.map (QuotientGroup.mk' (fixV H)))) : W ⧸ fixV H) =
          QuotientGroup.mk' (fixV H) ((f.symm u : ↥(commV R)) : W) := by
        rw [← hf, MulEquiv.apply_symm_apply]
      show QuotientGroup.mk' (fixV H) ((r : MulAut W) ((f.symm u : ↥(commV R)) : W)) =
        ((((secRes hRC hRS r : ↥(autSub (autQuot R (fixV H)) (U.map (QuotientGroup.mk' (fixV H))))) :
          MulAut ↥(U.map (QuotientGroup.mk' (fixV H)))) (u : ↥(U.map (QuotientGroup.mk' (fixV H)))) :
            ↥(U.map (QuotientGroup.mk' (fixV H)))) : W ⧸ fixV H)
      rw [secRes_apply, hu', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, quotHom_mk]
    rw [← key, MulEquiv.symm_apply_apply]

end Moves

theorem case_three_of_moves (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
    (hmin : rkIdx (fixV (Subgroup.zpowers t)) = E3.mParam Y) (hm : E3.mParam Y < dMinDeg ↥L)
    {U : Subgroup W} (hU : U ∈ irrSet H) (hLU : ¬ commSub U L ≤ fixV H)
    (htU : ¬ commSub U (Subgroup.zpowers t) ≤ fixV H)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) :
    ∃ (R : Subgroup (MulAut W)) (e : ℕ), R ≤ Y ∧ IsDirSumOver (conjSet R Y) commV ∧
      CFSG.Open.IsSubnormal L R ∧ IsNaturalO4Plus R e ∧ E3.mParam Y = e ∧
      dMinDeg ↥L = 2 * e := by
  have hm' : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L := hmin ▸ hm
  have hUt := hfix U hU
  obtain ⟨h1, -, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.1
  rcases local_cases hD hW hO hB hL hH ht ht2 hfix hm' hU hLU htU with
    ⟨hLt', -, -⟩ | ⟨-, hunU, e, hde, hnat, hrk⟩
  · exact absurd hLt' hmove
  obtain ⟨e', -, -, hrk', hsw⟩ := exists_o4_of_map_ne hD hW hL hH ht ht2 hm' hmove hU hUt hLU
  have hee : e' = e := hrk'.symm.trans hrk
  rw [hee] at hsw
  have hC0 := fixV_eq_bot_of_moves hD hW hL hH ht ht2 hfix hm' hmove hU hLU hO hB
  have hU0 := inf_fixV_eq_bot_of_moves hW hL hH ht ht2 hfix hm' hmove hU hLU
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨-, hLtH, -⟩ := conjSet_facts hL hH hLt
  have htoth : ∀ I ∈ irrSet H, I ≠ U → ∀ w ∈ I, t w = w := fun I hI hIU w hw =>
    le_centSub_of_moves hD hW hL hH ht ht2 hfix hm' hmove hU hLU hC0 hI hIU
      ((le_sup_right : _ ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ _) (Subgroup.mem_zpowers t))
      w hw
  have htrk : rkIdx (fixV (Subgroup.zpowers t)) = e := by
    rw [rkIdx_fixV_eq_rk_commSub htop hU0 (hstab ht) hUt htoth,
      rk_commSub_eq_rkIdx_autSub (hstab ht) hUt]
    exact hrk
  have hnormU := fun g (hg : g ∈ Y) (hUg : U.map g.toMonoidHom = U) =>
    map_conj_eq_of_moves hD hW hL hH ht ht2 hfix hm' hmove hU hLU hC0 hU0 htop hunU htrk hsw hg hUg
  exact ⟨_, e, sup_le (sup_le hL.1 (hLtH.trans hHY)) (Subgroup.zpowers_le.mpr ht),
    isDirSumOver_of_moves hD hW hL hH ht ht2 hfix hm' hmove hU hLU hC0 htop hunU hnormU,
    isSubnormal_sup_zpowers hL ht ht2' hmove,
    isNaturalO4Plus_of_moves hD hW hL hH ht ht2 hfix hm' hmove hU hLU hC0 hU0 htop hnat,
    hmin.symm.trans htrk, hde⟩

end CFSG.LocalAnalysis.WeakClosure81
