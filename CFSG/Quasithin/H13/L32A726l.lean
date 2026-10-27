module

public import CFSG.Quasithin.H13.L32A726k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def actComp_726 {G0 L0 : Subgroup G}
    (hn : G0 ≤ Subgroup.normalizer (L0 : Set G)) : ↥G0 →* MulAut ↥L0 :=
  (Subgroup.normalizerMonoidHom L0).comp (Subgroup.inclusion hn)

omit [Finite G] in
theorem actComp_of_mem_726 {G0 L0 : Subgroup G} (hn : G0 ≤ Subgroup.normalizer (L0 : Set G))
    {g : ↥G0} (hg : (g : G) ∈ L0) : actComp_726 hn g = MulAut.conj (⟨g, hg⟩ : ↥L0) := by
  ext ℓ
  rfl

omit [Finite G] in
theorem mul_conj_mul_inv_726 {A : Type*} [Group A] (σ : MulAut A) (m : A) :
    σ * MulAut.conj m * σ⁻¹ = MulAut.conj (σ m) := by
  ext a
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem center_le_pCoreOf_726 {G0 L0 : Subgroup G} (hodd : OddCoreModTwoTrivial G0)
    (hL0 : L0 ∈ cComp G0) : (Subgroup.center ↥L0).map L0.subtype ≤ pCoreOf 2 L0 := by
  rcases normal_eq_top_or_map_le_solvRad hL0 (Subgroup.center ↥L0) with h | h
  · exfalso
    refine not_isSolvable_of_mem_cComp hL0 (Group.isSolvable_of_comm fun a b => ?_)
    have ha : a ∈ Subgroup.center ↥L0 := by
      rw [h]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  · rwa [solvRad_eq_pCoreOf_of_mem_cComp hodd hL0] at h

omit [Finite G] in
theorem actComp_ne_one_726 {G0 L0 : Subgroup G} (hn : G0 ≤ Subgroup.normalizer (L0 : Set G))
    (hZ : (Subgroup.center ↥L0).map L0.subtype ≤ pCoreOf 2 L0) {g : ↥G0} (hg : (g : G) ∈ L0)
    (hg2 : (g : G) ∉ pCoreOf 2 L0) : actComp_726 hn g ≠ 1 := by
  intro h1
  rw [actComp_of_mem_726 hn hg] at h1
  refine hg2 (hZ ⟨⟨g, hg⟩, ?_, rfl⟩)
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro ℓ
  have h2 := congrArg (fun φ : MulAut ↥L0 => φ ℓ) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc ℓ * ⟨g, hg⟩ = (⟨g, hg⟩ * ℓ * (⟨g, hg⟩ : ↥L0)⁻¹) * ⟨g, hg⟩ := by rw [h2]
    _ = ⟨g, hg⟩ * ℓ := by group

section Ctx

variable {T L V H D : Subgroup G}

theorem f5_726 (hc : Ctx726 G T L V H D) {d : G} {Ld : Subgroup G}
    (hn : Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (Ld : Set G))
    (hZ : (Subgroup.center ↥Ld).map Ld.subtype ≤ pCoreOf 2 Ld)
    (hL1Ld : L32A.l1 T L V ≤ Ld) (hLdGd : Ld ≤ Subgroup.centralizer ({d} : Set G)) {x : G}
    (hxL1 : x ∈ L32A.l1 T L V) (hxHd : x ∈ H ⊓ Subgroup.centralizer ({d} : Set G)) :
    ∃ N : Subgroup (MulAut ↥Ld), N ≤ (MulAut.conj : ↥Ld →* MulAut ↥Ld).range ∧
      (actComp_726 hn).comp (Subgroup.inclusion
        (inf_le_right : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ _)) ⟨x, hxHd⟩ ∈ N ∧
      ((actComp_726 hn).comp (Subgroup.inclusion
        (inf_le_right : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ _))).range ≤
        Subgroup.normalizer (N : Set (MulAut ↥Ld)) ∧
      ∀ a ∈ (MulAut.conj : ↥Ld →* MulAut ↥Ld).range,
        a ∈ Subgroup.normalizer (N : Set (MulAut ↥Ld)) →
        a ∈ ((actComp_726 hn).comp (Subgroup.inclusion
          (inf_le_right : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ _))).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L32A.l1 T L V with hL₁
  set N : Subgroup (MulAut ↥Ld) := (L₁.subgroupOf Ld).map MulAut.conj with hN
  refine ⟨N, Subgroup.map_le_range _ _, ⟨⟨x, hL1Ld hxL1⟩, hxL1,
    (actComp_of_mem_726 hn (g := ⟨x, hxHd.2⟩) (hL1Ld hxL1)).symm⟩, ?_, ?_⟩
  ·
    have key : ∀ g : ↥(Subgroup.centralizer ({d} : Set G)), (g : G) ∈ H → ∀ a ∈ N,
        actComp_726 hn g * a * (actComp_726 hn g)⁻¹ ∈ N := by
      rintro g hgH _ ⟨m, hm, rfl⟩
      rw [mul_conj_mul_inv_726]
      exact ⟨actComp_726 hn g m, (Subgroup.mem_normalizer_iff.mp (hc.l1_normal hgH) m).mp hm,
        rfl⟩
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨key _ h.2.1 a, fun ha => ?_⟩
    have h1 := key (Subgroup.inclusion inf_le_right h)⁻¹ (H.inv_mem h.2.1) _ ha
    rwa [map_inv, inv_inv, MonoidHom.comp_apply, show ∀ σ : MulAut ↥Ld,
      σ⁻¹ * (σ * a * σ⁻¹) * σ = a from fun σ => by group] at h1
  ·
    rintro _ ⟨ℓ₀, rfl⟩ hnorm
    set Z : Subgroup G := (Subgroup.center ↥Ld).map Ld.subtype with hZdef
    have hZ2 : IsPGroup 2 Z := (pCoreOf_isPGroup 2 Ld).to_le hZ
    have hZc : ∀ c ∈ Z, ∀ ℓ ∈ Ld, c * ℓ = ℓ * c := by
      rintro _ ⟨c, hc', rfl⟩ ℓ hℓ
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨ℓ, hℓ⟩).symm
    have hZC : Z ≤ Subgroup.centralizer (L₁ : Set G) := fun c hcZ =>
      Subgroup.mem_centralizer_iff.mpr fun m hm => (hZc c hcZ m (hL1Ld hm)).symm
    have hZN : Z ≤ Subgroup.normalizer (L₁ : Set G) :=
      hZC.trans (Subgroup.centralizer_le_normalizer _)
    have hl1 : oTwoUpper L₁ = L₁ := by
      rw [hL₁, hc.l1_eq]
      exact A4.oTwoUpper_oTwoUpper _
    have hO2 : oTwoUpper (L₁ ⊔ Z) = L₁ := by
      apply le_antisymm
      · exact oTwoUpper_le_of_pow_mem fun g hg => E1.exists_pow_mem_of_mem_sup hZ2 hZN hg
      · calc L₁ = oTwoUpper L₁ := hl1.symm
          _ ≤ oTwoUpper (L₁ ⊔ Z) := oTwoUpper_mono le_sup_left
    have key : ∀ ℓ : ↥Ld, MulAut.conj ℓ ∈ Subgroup.normalizer (N : Set (MulAut ↥Ld)) →
        ∀ y ∈ L₁ ⊔ Z, (ℓ : G) * y * (ℓ : G)⁻¹ ∈ L₁ ⊔ Z := by
      intro ℓ hℓ y hy
      have hle : L₁ ⊔ Z ≤ (L₁ ⊔ Z).comap (MulAut.conj (ℓ : G)).toMonoidHom := by
        refine sup_le (fun m hm => ?_) (fun c hcZ => ?_)
        · have hmN : MulAut.conj (⟨m, hL1Ld hm⟩ : ↥Ld) ∈ N := ⟨⟨m, hL1Ld hm⟩, hm, rfl⟩
          have h1 := (Subgroup.mem_normalizer_iff.mp hℓ _).mp hmN
          rw [mul_conj_mul_inv_726] at h1
          obtain ⟨m', hm', hm'eq⟩ := h1
          set w : ↥Ld := MulAut.conj ℓ ⟨m, hL1Ld hm⟩ with hw
          have hcen : m'⁻¹ * w ∈ Subgroup.center ↥Ld := by
            rw [Subgroup.mem_center_iff]
            intro q
            have h2 := congrArg (fun σ : MulAut ↥Ld => σ q) hm'eq
            simp only [MulAut.conj_apply] at h2
            calc q * (m'⁻¹ * w) = m'⁻¹ * (m' * q * m'⁻¹) * w := by group
              _ = m'⁻¹ * (w * q * w⁻¹) * w := by rw [h2]
              _ = m'⁻¹ * w * q := by group
          show (ℓ : G) * m * (ℓ : G)⁻¹ ∈ L₁ ⊔ Z
          have hwG : ((w : ↥Ld) : G) = (ℓ : G) * m * (ℓ : G)⁻¹ := rfl
          rw [← hwG, show (w : G) = (m' : G) * ((m'⁻¹ * w : ↥Ld) : G) by simp]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show (m' : G) ∈ L₁ from hm'))
            (Subgroup.mem_sup_right ⟨_, hcen, rfl⟩)
        · show (ℓ : G) * c * (ℓ : G)⁻¹ ∈ L₁ ⊔ Z
          rw [← hZc c hcZ ℓ ℓ.2, mul_inv_cancel_right]
          exact Subgroup.mem_sup_right hcZ
      exact hle hy
    have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer ((L₁ ⊔ Z : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨key ℓ₀ hnorm y, fun hy => ?_⟩
      have h := key ℓ₀⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hnorm) _ hy
      rwa [show ((ℓ₀⁻¹ : ↥Ld) : G) * ((ℓ₀ : G) * y * (ℓ₀ : G)⁻¹) * ((ℓ₀⁻¹ : ↥Ld) : G)⁻¹ = y by
        simp [mul_assoc]] at h
    have hℓ₀L1 : (ℓ₀ : G) ∈ Subgroup.normalizer (L₁ : Set G) := by
      have h := normalizer_le_normalizer_oTwoUpper _ hℓ₀N
      rwa [hO2] at h
    exact ⟨⟨ℓ₀, normalizer_l1_le_726 hc hℓ₀L1, hLdGd ℓ₀.2⟩,
      actComp_of_mem_726 hn (g := ⟨ℓ₀, hLdGd ℓ₀.2⟩) ℓ₀.2⟩

theorem centralizer_le_726 (hC129 : ASC129Statement G) (h121 : Id2519.Prop121Three)
    (hC27 : KG14726C27C) (h3x : NQCore.Prop134ThreeExtraspecial) (hlist : Lemma115_3_List)
    (hSz : KG14726Sz) (hL115 : KG14726L115C) (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    Subgroup.centralizer ({d} : Set G) ≤ H := by
  by_contra hGdH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, Y, E₁, E₂, hX⟩ := exists_xData_726 hc
  obtain ⟨Ld, hLd, hxLd, hn⟩ :=
    exists_normal_component_726 hC129 h121 hC27 h3x hlist hSz hc hdD hdV hd2 htT htd hGdH hX
  obtain ⟨z, hzV, hz1, hz2, hzT, hzc, hzH⟩ := exists_z_726 hc hdD hdV
  have hyp := lemma115Hyp_726 hc hdD hdV hd2 htT htd hz1 hz2 hzT hzc hzH
  have hodd := oddCoreModTwoTrivial_gd_726 hC129 h3x hc hdD hdV hd2 htT htd hGdH
  have hQ := pCoreOf_h_le_td_of_g0_726 h3x hc hdD hdV hd2 htT htd inf_le_right le_rfl hGdH
  have hLdc := Id2519.mem_cComp_of_isComponentIn hLd
  have := hc.setting.hyp.fsu.simple
  obtain ⟨-, hcomm, -, hcases⟩ := hlist.component_cases hc.setting.hyp.fsu.simple
    hc.setting.hyp.fsu.nonabelian
    (QuasithinUnique.qtkeCore_of_cat hc.setting.hyp.fsu.nonabelian hc.setting.hyp.fsu.qtke) hyp
    hLd
  have h3 := three_dvd_card_of_isComponentIn_726 h121 hlist hSz hc hdD hdV hd2 hyp hX hLd
  have hZ := center_le_pCoreOf_726 hodd hLdc
  have hLdGd := hLd.1
  have hxHd : x ∈ H ⊓ Subgroup.centralizer ({d} : Set G) :=
    k_le_hd_726 hc hdD (l1_le_k_726 hc hX.x_mem)
  have hL1Ld : L32A.l1 T L V ≤ Ld := by
    refine (l1_le_conjClosure_726 hc hX.x_mem hX.x_order).trans
      (conjClosure_le fun p hp w hw => ?_)
    have hpN : p ∈ Subgroup.normalizer (Ld : Set G) :=
      hn (((k_le_hd_726 hc hdD).trans inf_le_right) ((l1_le_k_726 hc) (pCoreOf_le 2 _ hp)))
    exact (Subgroup.mem_normalizer_iff.mp hpN w).mp ((Subgroup.zpowers_le.mpr hxLd) hw)
  set φ := actComp_726 hn with hφ
  set ψ : ↥(H ⊓ Subgroup.centralizer ({d} : Set G)) →* MulAut ↥Ld :=
    φ.comp (Subgroup.inclusion inf_le_right) with hψ
  have hψx : ∀ hx : x ∈ H ⊓ Subgroup.centralizer ({d} : Set G), ψ ⟨x, hx⟩ ≠ 1 := fun hx' =>
    actComp_ne_one_726 hn hZ (g := ⟨x, hx'.2⟩) hxLd (not_mem_pCoreOf_726 hX.x_order)
  have hInn : (MulAut.conj : ↥Ld →* MulAut ↥Ld).range ≤ φ.range := by
    rintro _ ⟨ℓ, rfl⟩
    exact ⟨⟨ℓ, hLdGd ℓ.2⟩, actComp_of_mem_726 hn (g := ⟨ℓ, hLdGd ℓ.2⟩) ℓ.2⟩
  have hBA : ψ.range ≤ φ.range := by
    rintro _ ⟨h, rfl⟩
    exact ⟨_, rfl⟩
  have hzK : z ∈ oTwoUpper H := hc.d_le (hc.v1_le_d hzV)
  have hzHd : z ∈ H ⊓ Subgroup.centralizer ({d} : Set G) :=
    ⟨(k_le_hd_726 hc hdD hzK).1,
      Subgroup.mem_centralizer_singleton_iff.mpr (hc.d_comm d hdD z hzK).symm⟩
  have hζ1 : ψ ⟨z, hzHd⟩ ≠ 1 := by
    intro h1
    have hzc' : ∀ ℓ ∈ Ld, z * ℓ = ℓ * z := fun ℓ hℓ => by
      have h2 := congrArg (fun σ : MulAut ↥Ld => ((σ ⟨ℓ, hℓ⟩ : ↥Ld) : G)) h1
      change z * ℓ * z⁻¹ = ℓ at h2
      calc z * ℓ = (z * ℓ * z⁻¹) * z := by group
        _ = ℓ * z := by rw [h2]
    apply ne_bot_of_mem_cComp hLdc
    rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
    intro ℓ hℓ w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Commute.zpow_right (hzc' ℓ hℓ).symm k).eq
  have hζc : ∀ b ∈ ψ.range, b * ψ ⟨z, hzHd⟩ = ψ ⟨z, hzHd⟩ * b := by
    rintro _ ⟨h, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hh : (h : G) ∈ Subgroup.centralizer ({z} : Set G) := hzH ▸ h.2.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hh
  have hF2p : ∀ ℓ : ↥Ld, (ℓ : G) * z = z * ℓ → MulAut.conj ℓ ∈ ψ.range := fun ℓ hℓz => by
    have hℓH : (ℓ : G) ∈ H := hzH ▸ Subgroup.mem_centralizer_singleton_iff.mpr hℓz
    exact ⟨⟨ℓ, hℓH, hLdGd ℓ.2⟩, actComp_of_mem_726 hn (g := ⟨ℓ, hLdGd ℓ.2⟩) ℓ.2⟩
  exact hL115 G Ld z hcases (BenderBranch.isQuasisimple_of_isComponentIn hLd) h3 φ.range hInn
    ψ.range hBA
    (not_two_dvd_index_range_726 (isSylowTwoOf_td_726 hc hdD hdV htT htd) (td_le_hd_726 hc d)
      inf_le_right φ)
    (card_range_726 hc hdD hX rfl ψ hψx)
    ⟨ψ ⟨x, hxHd⟩, ⟨_, (actComp_of_mem_726 hn (g := ⟨x, hxHd.2⟩) hxLd).symm⟩,
      orderOf_map_eq_three_726 hX.x_order hxHd ψ (hψx hxHd), ⟨⟨x, hxHd⟩, rfl⟩,
      fun _ => f5_726 hc hn hZ hL1Ld hLdGd hX.x_mem hxHd,
      range_le_normalizer_726 hc hdD hdV hQ hX rfl ψ hψx hxHd⟩
    ⟨ψ ⟨z, hzHd⟩, ⟨⟨z, hzHd⟩, rfl⟩, hζ1, fun ℓ => rfl, hζc⟩ hF2p
    (isPOnePlusTwo_range_726 hc hdD hX rfl ψ hψx)

end Ctx

end CFSG.Quasithin.H13.L32A
