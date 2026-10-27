module

public import CFSG.Quasithin.EmptyFaithful.S153E55D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E55

open CFSG.Quasithin.S153E

section PartA

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem centerOf_P_le_V (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) :
    centerOf (Pgp153 T M V₁ Mc g) ≤ VZ T M := by
  have hV := cx.c.hyp.elemAbelian
  have hI := c.h54.one
  have pd := pdecomp cx c
  obtain ⟨y₁, y₂, hy₁Y, hy₂Y, hy₁o, hy₂o, hy₁f, hy₂f, hy₁N, hy₂N, hc₁₂, hYc⟩ :=
    exists_y12 h113 cx c
  have hy₁YU : y₁ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy₁Y
  have hy₂YU : y₂ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy₂Y
  have hVA : VZ T M ≤ centerOf (Pgp153 T M V₁ Mc g) := c.h54.two_center
  have hAP : ∀ a ∈ centerOf (Pgp153 T M V₁ Mc g), ∀ p ∈ Pgp153 T M V₁ Mc g, a * p = p * a :=
    fun a ha p hp => (Subgroup.mem_centralizer_iff.mp ha.2 p hp).symm
  have hAab : ∀ a ∈ centerOf (Pgp153 T M V₁ Mc g), ∀ b ∈ centerOf (Pgp153 T M V₁ Mc g), a * b = b * a :=
    fun a ha b hb => hAP a ha b hb.1
  have hP2 : IsPGroup 2 (Pgp153 T M V₁ Mc g) := P_isPGroup hI
  have hA2 : IsPGroup 2 (centerOf (Pgp153 T M V₁ Mc g)) := hP2.to_le inf_le_left
  have hYUA : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤
      Subgroup.normalizer ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G) :=
    (YU_le_normalizer_P hI).trans (normalizer_le_normalizer_centerOf _)
  have hTA : T ≤ Subgroup.normalizer ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G) :=
    (T_le_normalizer_P hI cx).trans (normalizer_le_normalizer_centerOf _)
  have hy₁A := hYUA hy₁YU
  have hy₂A := hYUA hy₂YU
  have hVN : ∀ y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc, y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    fun y hy => YU_le_normalizer_V cx hy
  have hsqP : ∀ a ∈ Pgp153 T M V₁ Mc g, a * a ∈ VZ T M :=
    fun a ha => pd.sq_mem_V (sq_mem_of_nat c.h54.four_nat₁) (sq_mem_of_nat c.h54.four_nat₂) ha
  have hV2 : ∀ v ∈ VZ T M, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV.2 v hv
  have h3G : ∀ d ∈ ⁅centerOf (Pgp153 T M V₁ Mc g), Subgroup.zpowers y₂⁆,
      y₁ * d * y₁⁻¹ * d⁻¹ ∈ VZ T M := by
    intro d hd
    have hdP₂ : d ∈ Pi153 T Mc M V₁ N₂ g := by
      refine (Subgroup.commutator_le.2 (fun a ha z hz => ?_)) hd
      have hzN : z ∈ Ni153 T Mc M V₁ N₂ := (Subgroup.zpowers_le.mpr hy₂N) hz
      have := pd.comm_mem_P₂ ha.1 hzN
      simpa [commutatorElement_def] using this
    have h0 := hdP₂
    rw [pd.cent₂] at h0
    have h := h0.2.2 y₁ hy₁N
    have e : y₁ * d * y₁⁻¹ * d⁻¹ = (d * y₁ * d⁻¹ * y₁⁻¹)⁻¹ := by group
    rw [e]
    exact (VZ T M).inv_mem h
  have hsq1 : ∀ a ∈ centerOf (Pgp153 T M V₁ Mc g), a * a = 1 :=
    sq_eq_one_of_decomp hAab hA2 hVA (fun a ha => hsqP a ha.1) hV2 hy₂A hy₂o hy₁f hy₂f h3G
  have hAe : IsElemAbelian 2 (centerOf (Pgp153 T M V₁ Mc g)) := isElemAbelian_centerOf hsq1
  have hWsq : ∀ w : IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe, w ^ 2 = 1 := IntMod.sq_eq_one
  have hconvcomm : ∀ (u u' : G) (hu : u ∈ Subgroup.normalizer
      ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G))
      (hu' : u' ∈ Subgroup.normalizer ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)),
      u * u' * u⁻¹ * u'⁻¹ ∈ Pgp153 T M V₁ Mc g →
      convI hAe ⟨u, hu⟩ * convI hAe ⟨u', hu'⟩ = convI hAe ⟨u', hu'⟩ * convI hAe ⟨u, hu⟩ := by
    intro u u' hu hu' hcu
    ext w
    refine IntMod.val_injective ?_
    simp only [MulAut.mul_apply, convI_apply_val]
    exact conj_commute_on_center hAP hcu hu hu' w.val_mem
  have hbarodd : ∀ (u : G) (hu : u ∈ Subgroup.normalizer
      ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)), Odd (orderOf u) →
      Odd (orderOf (convI hAe ⟨u, hu⟩)) := by
    intro u hu ho
    refine Odd.of_dvd_nat ho ?_
    have := orderOf_map_dvd (convI hAe) (⟨u, hu⟩ : Subgroup.normalizer
      ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G))
    rwa [Subgroup.orderOf_mk] at this
  let V' : Subgroup (IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe) :=
    (VZ T M).comap (inclMod hAe)
  have hmemV' : ∀ w : IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe, w ∈ V' ↔ w.val ∈ VZ T M :=
    fun w => Iff.rfl
  have hVinv : ∀ (u : G) (hu : u ∈ Subgroup.normalizer
      ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)),
      u ∈ Subgroup.normalizer (VZ T M : Set G) →
      ∀ g' ∈ Subgroup.zpowers (convI hAe ⟨u, hu⟩), ∀ v ∈ V', g' v ∈ V' := by
    intro u hu huV g' hg' v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    have hk : (convI hAe ⟨u, hu⟩) ^ k = convI hAe (⟨u, hu⟩ ^ k) := (map_zpow _ _ _).symm
    rw [hk, hmemV', convI_apply_val]
    have e : ((⟨u, hu⟩ ^ k : Subgroup.normalizer
        ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)) : G) = u ^ k := by simp
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ huV k) v.val).mp
      ((hmemV' v).1 hv)
  have hfpf : ∀ (u : G) (hu : u ∈ Subgroup.normalizer
      ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)),
      (∀ v ∈ VZ T M, u * v * u⁻¹ = v → v = 1) →
      ∀ v ∈ V', convI hAe ⟨u, hu⟩ v = v → v = 1 := by
    intro u hu hf v hv hvv
    have h1 := congrArg IntMod.val hvv
    rw [convI_apply_val] at h1
    exact IntMod.val_injective (hf _ ((hmemV' v).1 hv) h1)
  have h3W : ∀ d ∈ commV (Subgroup.zpowers (convI hAe ⟨y₂, hy₂A⟩)),
      commHom (convI hAe ⟨y₁, hy₁A⟩) d ∈ V' := by
    have hK : commV (Subgroup.zpowers (convI hAe ⟨y₂, hy₂A⟩)) ≤
        (Pi153 T Mc M V₁ N₂ g).comap (inclMod hAe) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, hx, w, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hk : (convI hAe ⟨y₂, hy₂A⟩) ^ k = convI hAe (⟨y₂, hy₂A⟩ ^ k) := (map_zpow _ _ _).symm
      have hyk : y₂ ^ k ∈ Ni153 T Mc M V₁ N₂ := Subgroup.zpow_mem _ hy₂N k
      have hwP : w.val ∈ Pgp153 T M V₁ Mc g := w.val_mem.1
      have h1 := pd.comm_mem_P₂ hwP hyk
      have h2 := (Pi153 T Mc M V₁ N₂ g).inv_mem h1
      rw [SetLike.mem_coe, Subgroup.mem_comap, hk]
      show ((convI hAe (⟨y₂, hy₂A⟩ ^ k) w * w⁻¹ : IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe).val) ∈ _
      rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv]
      have e : ((⟨y₂, hy₂A⟩ ^ k : Subgroup.normalizer
          ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)) : G) = y₂ ^ k := by simp
      rw [e]
      have e2 : y₂ ^ k * w.val * (y₂ ^ k)⁻¹ * w.val⁻¹ =
          (w.val * y₂ ^ k * w.val⁻¹ * (y₂ ^ k)⁻¹)⁻¹ := by group
      rw [e2]
      exact h2
    intro d hd
    have hdP₂ : d.val ∈ Pi153 T Mc M V₁ N₂ g := hK hd
    rw [hmemV', commHom_apply, IntMod.val_mul, convI_apply_val, IntMod.val_inv]
    have h0 := hdP₂
    rw [pd.cent₂] at h0
    have h := h0.2.2 y₁ hy₁N
    have e : y₁ * d.val * y₁⁻¹ * d.val⁻¹ = (d.val * y₁ * d.val⁻¹ * y₁⁻¹)⁻¹ := by group
    show y₁ * d.val * y₁⁻¹ * d.val⁻¹ ∈ VZ T M
    rw [e]
    exact (VZ T M).inv_mem h
  set C : Subgroup (IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe) :=
    fixV (Subgroup.zpowers (convI hAe ⟨y₁, hy₁A⟩)) ⊔
      fixV (Subgroup.zpowers (convI hAe ⟨y₂, hy₂A⟩)) with hC
  obtain ⟨hinf, hsup⟩ : V' ⊓ C = ⊥ ∧ V' ⊔ C = ⊤ :=
    exists_compl hWsq (hconvcomm y₁ y₂ hy₁A hy₂A hc₁₂) (hbarodd y₁ hy₁A hy₁o)
      (hbarodd y₂ hy₂A hy₂o) (hVinv y₁ hy₁A (hVN y₁ hy₁YU)) (hfpf y₁ hy₁A hy₁f)
      (hfpf y₂ hy₂A hy₂f) h3W
  have key : ∀ (tt : G) (htT : tt ∈ T) (yi : G) (hyiY : yi ∈ Y153 Mc M),
      (∀ v ∈ VZ T M, yi * v * yi⁻¹ = v → v = 1) →
      ∀ a : IntMod (centerOf (Pgp153 T M V₁ Mc g)) hAe,
        convI hAe ⟨yi, hYUA (Y_le_YU hyiY)⟩ a = a →
        convI hAe ⟨tt, hTA htT⟩ a ∈ C := by
    intro tt htT yi hyiY hfi a ha
    have hyiA : yi ∈ Subgroup.normalizer ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G) :=
      hYUA (Y_le_YU hyiY)
    have hy'Y : tt * yi * tt⁻¹ ∈ Y153 Mc M :=
      (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_Y cx htT) yi).mp hyiY
    have hy'YU : tt * yi * tt⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy'Y
    have hy'A := hYUA hy'YU
    have hcom₁ : convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩ * convI hAe ⟨y₁, hy₁A⟩ =
        convI hAe ⟨y₁, hy₁A⟩ * convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩ :=
      hconvcomm _ _ hy'A hy₁A (hYc _ hy'Y).1
    have hcom₂ : convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩ * convI hAe ⟨y₂, hy₂A⟩ =
        convI hAe ⟨y₂, hy₂A⟩ * convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩ :=
      hconvcomm _ _ hy'A hy₂A (hYc _ hy'Y).2
    have hbar : convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩ =
        convI hAe ⟨tt, hTA htT⟩ * convI hAe ⟨yi, hyiA⟩ * (convI hAe ⟨tt, hTA htT⟩)⁻¹ := by
      have e : (⟨tt * yi * tt⁻¹, hy'A⟩ : Subgroup.normalizer
          ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G)) =
          ⟨tt, hTA htT⟩ * ⟨yi, hyiA⟩ * ⟨tt, hTA htT⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv]
    refine mem_of_fixed hinf hsup (y' := convI hAe ⟨tt * yi * tt⁻¹, hy'A⟩) ?_ ?_ ?_ ?_
    · intro v hv
      exact hVinv _ hy'A (hVN _ hy'YU) _ (Subgroup.mem_zpowers _) v hv
    · exact invariant_sup_fixV hcom₁ hcom₂
    · refine hfpf _ hy'A ?_
      intro v hv hvv
      have hv' : tt⁻¹ * v * tt⁻¹⁻¹ ∈ VZ T M :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (T_le_N cx htT)) v).mp hv
      have h1 : yi * (tt⁻¹ * v * tt⁻¹⁻¹) * yi⁻¹ = tt⁻¹ * v * tt⁻¹⁻¹ := by
        have e : yi * (tt⁻¹ * v * tt⁻¹⁻¹) * yi⁻¹ =
            tt⁻¹ * ((tt * yi * tt⁻¹) * v * (tt * yi * tt⁻¹)⁻¹) * tt⁻¹⁻¹ := by group
        rw [e, hvv]
      have h2 := hfi _ hv' h1
      have e : v = tt * (tt⁻¹ * v * tt⁻¹⁻¹) * tt⁻¹ := by group
      rw [e, h2]
      group
    · rw [hbar]
      have e : (convI hAe ⟨tt, hTA htT⟩ * convI hAe ⟨yi, hyiA⟩ * (convI hAe ⟨tt, hTA htT⟩)⁻¹)
          (convI hAe ⟨tt, hTA htT⟩ a) = convI hAe ⟨tt, hTA htT⟩ (convI hAe ⟨yi, hyiA⟩ a) := by
        simp [MulAut.mul_apply]
      rw [e, ha]
  have hCT : ∀ (tt : G) (htT : tt ∈ T), ∀ w ∈ C, convI hAe ⟨tt, hTA htT⟩ w ∈ C := by
    intro tt htT w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul]
    exact Subgroup.mul_mem _ (key tt htT y₁ hy₁Y hy₁f a (mem_fixV_zpowers_iff.mp ha))
      (key tt htT y₂ hy₂Y hy₂f b (mem_fixV_zpowers_iff.mp hb))
  have hCbot : C = ⊥ := by
    by_contra hne
    have hT2 : IsPGroup 2 T := cx.c.hyp.isSylowTwoOf.2.1
    have hB : IsPGroup 2 (autI hAe T) := by
      have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer
          ((centerOf (Pgp153 T M V₁ Mc g) : Subgroup G) : Set G))) :=
        hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTA).symm
      exact h1.map (convI hAe)
    obtain ⟨c0, hc0C, hc01, hc0fix⟩ := B1.exists_fixed_ne_one hWsq hB (M := C)
      (fun b hb m hm => by
        obtain ⟨x, hxT, rfl⟩ := (mem_autI hAe).1 hb
        exact hCT x.1 hxT m hm) hne
    have hcentT : c0.val ∈ Subgroup.centralizer (T : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have h1 := congrArg IntMod.val (hc0fix _ (convI_mem_autI hAe hx (hTA hx)))
      rw [convI_apply_val] at h1
      calc x * c0.val = (x * c0.val * x⁻¹) * x := by group
        _ = c0.val * x := by rw [show x * c0.val * x⁻¹ = c0.val from h1]
    have hc0T : c0.val ∈ T := P_le_T hI cx c0.val_mem.1
    have hc0sq : c0.val * c0.val = 1 := hsq1 _ c0.val_mem
    have hc0Z : c0.val ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨hc0T, hcentT⟩, by rw [pow_two]; exact hc0sq⟩
    have hc0V : c0 ∈ V' := (hmemV' c0).2 (cx.c.hyp.Z_le_VZ hc0Z)
    have h4 : c0 ∈ V' ⊓ C := ⟨hc0V, hc0C⟩
    rw [hinf, Subgroup.mem_bot] at h4
    exact hc01 h4
  intro a ha
  have hw : IntMod.mk hAe ⟨a, ha⟩ ∈ V' ⊔ C := by
    rw [hsup]
    exact Subgroup.mem_top _
  rw [hCbot, sup_bot_eq] at hw
  exact (hmemV' _).1 hw

end PartA

end S153E55

end CFSG.Quasithin
