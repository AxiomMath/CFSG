module

public import CFSG.Quasithin.H13.NQSetupTwoStabilizer
public import CFSG.LieType.SteinbergBRTransvectionStabilizers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQSetup

open Module Subgroup CFSG.QuasithinUnique.Setup.Offender

theorem card_orbit_mul_card_stabilizer' {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (x : X) : Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
      Nat.card G := by
  rw [← (MulAction.stabilizer G x).card_mul_index, MulAction.index_stabilizer,
    Nat.card_coe_set_eq, mul_comm]

theorem not_four_dvd_card_orbit_of_le {G X : Type*} [Group G] [MulAction G X] {S H : Subgroup G}
    [Finite H] (hSH : S ≤ H) (x : X) (hidx : ¬ 4 ∣ (S.subgroupOf H).index)
    (hodd : Odd (Nat.card (MulAction.orbit S x))) :
    ¬ 4 ∣ Nat.card (MulAction.orbit H x) := by
  have : Finite S :=
    Finite.of_injective (Subgroup.inclusion hSH) (Subgroup.inclusion_injective hSH)
  have hH := card_orbit_mul_card_stabilizer' (G := H) x
  have hS := card_orbit_mul_card_stabilizer' (G := S) x
  have hHS : Nat.card H = (S.subgroupOf H).index * Nat.card S := by
    rw [← (S.subgroupOf H).card_mul_index, mul_comm,
      Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv]
  have hdvd : Nat.card (MulAction.stabilizer S x) ∣ Nat.card (MulAction.stabilizer H x) := by
    let f : MulAction.stabilizer S x →* MulAction.stabilizer H x :=
      { toFun := fun s => ⟨Subgroup.inclusion hSH s, by
          have := s.2
          rw [MulAction.mem_stabilizer_iff] at this ⊢
          exact this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h => by
      have := congrArg (fun y : MulAction.stabilizer H x => ((y : H) : G)) h
      exact Subtype.ext (Subtype.ext this)
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < Nat.card (MulAction.stabilizer S x) := Nat.card_pos
  have key : Nat.card (MulAction.orbit H x) * c =
      (S.subgroupOf H).index * Nat.card (MulAction.orbit S x) := by
    have h1 : Nat.card (MulAction.orbit H x) * c * Nat.card (MulAction.stabilizer S x) =
        (S.subgroupOf H).index * Nat.card (MulAction.orbit S x) *
          Nat.card (MulAction.stabilizer S x) := by
      calc Nat.card (MulAction.orbit H x) * c * Nat.card (MulAction.stabilizer S x)
          = Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) := by
            rw [hc]
            ring
        _ = _ := by rw [hH, hHS, ← hS]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  intro h4
  apply hidx
  have h4' : 4 ∣ (S.subgroupOf H).index * Nat.card (MulAction.orbit S x) :=
    key ▸ Dvd.dvd.mul_right h4 c
  have hcop : Nat.Coprime 4 (Nat.card (MulAction.orbit S x)) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  exact hcop.dvd_of_dvd_mul_right h4'

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

noncomputable def normalizerQuotientAdd {V : Type*} [AddCommGroup V]
    {S : Subgroup (E ≃ₗ[ZMod 2] E)} (φ : E →+ V) (hφ : Function.Surjective φ)
    (hker : ∀ e, e ∈ fixGL S ↔ φ e = 0) {g : E ≃ₗ[ZMod 2] E}
    (hg : g ∈ normalizer (S : Set (E ≃ₗ[ZMod 2] E))) : V →+ V :=
  φ.liftOfSurjective hφ ⟨φ.comp (g : E →ₗ[ZMod 2] E).toAddMonoidHom, fun e he => by
    rw [AddMonoidHom.mem_ker] at he ⊢
    exact (hker _).1 (SteinbergBS.normalizer_map_mem_fixGL hg ((hker e).2 he))⟩

theorem normalizerQuotientAdd_apply {V : Type*} [AddCommGroup V]
    {S : Subgroup (E ≃ₗ[ZMod 2] E)} (φ : E →+ V) (hφ : Function.Surjective φ)
    (hker : ∀ e, e ∈ fixGL S ↔ φ e = 0) {g : E ≃ₗ[ZMod 2] E}
    (hg : g ∈ normalizer (S : Set (E ≃ₗ[ZMod 2] E))) (e : E) :
    normalizerQuotientAdd φ hφ hker hg (φ e) = φ (g e) :=
  φ.liftOfRightInverse_comp_apply (Function.surjInv hφ) (Function.rightInverse_surjInv hφ) _ e

noncomputable def normalizerQuotientHom {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subgroup (E ≃ₗ[ZMod 2] E)) (φ : E →+ V) (hφ : Function.Surjective φ)
    (hker : ∀ e, e ∈ fixGL S ↔ φ e = 0) :
    normalizer (S : Set (E ≃ₗ[ZMod 2] E)) →* (V ≃ₗ[ZMod 2] V) where
  toFun g :=
    { toFun := normalizerQuotientAdd φ hφ hker g.2
      map_add' := map_add _
      map_smul' := fun c v => ZMod.map_smul (normalizerQuotientAdd φ hφ hker g.2) c v
      invFun := normalizerQuotientAdd φ hφ hker (inv_mem g.2)
      left_inv := fun v => by
        obtain ⟨e, rfl⟩ := hφ v
        rw [normalizerQuotientAdd_apply, normalizerQuotientAdd_apply]
        congr 1
        exact (g : E ≃ₗ[ZMod 2] E).symm_apply_apply e
      right_inv := fun v => by
        obtain ⟨e, rfl⟩ := hφ v
        rw [normalizerQuotientAdd_apply, normalizerQuotientAdd_apply]
        congr 1
        exact (g : E ≃ₗ[ZMod 2] E).apply_symm_apply e }
  map_one' := LinearEquiv.ext fun v => by
    obtain ⟨e, rfl⟩ := hφ v
    change normalizerQuotientAdd φ hφ hker (one_mem _) (φ e) = φ e
    rw [normalizerQuotientAdd_apply]
    rfl
  map_mul' g g' := LinearEquiv.ext fun v => by
    obtain ⟨e, rfl⟩ := hφ v
    change normalizerQuotientAdd φ hφ hker (mul_mem g.2 g'.2) (φ e) =
      normalizerQuotientAdd φ hφ hker g.2 (normalizerQuotientAdd φ hφ hker g'.2 (φ e))
    rw [normalizerQuotientAdd_apply, normalizerQuotientAdd_apply, normalizerQuotientAdd_apply]
    rfl

theorem normalizerQuotientHom_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subgroup (E ≃ₗ[ZMod 2] E)) (φ : E →+ V) (hφ : Function.Surjective φ)
    (hker : ∀ e, e ∈ fixGL S ↔ φ e = 0) (g : normalizer (S : Set (E ≃ₗ[ZMod 2] E))) (e : E) :
    normalizerQuotientHom S φ hφ hker g (φ e) = φ ((g : E ≃ₗ[ZMod 2] E) e) :=
  normalizerQuotientAdd_apply φ hφ hker g.2 e

theorem mem_fixGL_iff_of_natural {V : Type*} [AddCommGroup V] {S : Subgroup (E ≃ₗ[ZMod 2] E)}
    (ρ : S → V → V) (φ : E →+ V)
    (heq : ∀ (s : S) (e : E), φ ((s : E ≃ₗ[ZMod 2] E) e) = ρ s (φ e))
    (hker : ∀ s ∈ S, ∀ e : E, φ e = 0 → s e = e)
    (hfix : ∀ v : V, (∀ s : S, ρ s v = v) → v = 0) (e : E) : e ∈ fixGL S ↔ φ e = 0 := by
  refine ⟨fun he => hfix _ fun s => ?_, fun he => mem_fixGL.2 fun s hs => hker s hs e he⟩
  rw [← heq, mem_fixGL.1 he s s.2]

theorem eq_zero_of_forall_specialLinear_apply_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (hV : finrank k V = 2) {v : V}
    (hv : ∀ u : SpecialLinearGroup k V, u v = v) : v = 0 := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  by_contra hv0
  obtain ⟨f, w, hfw, hne⟩ := exists_transvection_apply_ne (K := k) (by omega) hv0
  exact hne (hv ⟨LinearEquiv.transvection hfw, LinearEquiv.transvection.det_eq_one hfw⟩)

theorem eq_zero_of_forall_linearEquiv_apply_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : 2 ≤ finrank K V) {v : V}
    (hv : ∀ u : V ≃ₗ[K] V, u v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨f, w, hfw, hne⟩ := exists_transvection_apply_ne hV hv0
  exact hne (hv _)

theorem nq_natural_trivial_kernel_extension_orbit_two_bound [FiniteDimensional (ZMod 2) E]
    (S H : Subgroup (E ≃ₗ[ZMod 2] E)) (hSH : S ≤ H)
    (hHN : H ≤ normalizer (S : Set (E ≃ₗ[ZMod 2] E))) (hES : commGL S ⊤ = ⊤)
    (hcond : ExplicitNaturalFour S ∨ ExplicitNaturalThreeExtension S) (e : E) :
    ¬ 4 ∣ Nat.card (MulAction.orbit H e) := by
  classical
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have : Finite (E ≃ₗ[ZMod 2] E) :=
    Finite.of_injective (fun g : E ≃ₗ[ZMod 2] E => (g : E → E)) DFunLike.coe_injective
  have hSN : S ≤ normalizer (S : Set (E ≃ₗ[ZMod 2] E)) := le_normalizer
  rcases hcond with h | h
  ·
    obtain ⟨k, _, _, hk, V, _, _, hV, β, φ, hφ, heq, hker⟩ := h
    have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
    have h2 : (1 + 1 : k) = 0 := SteinbergCB.field_four_two hk
    let _ : Module (ZMod 2) V := AddCommGroup.zmodModule fun v => by
      rw [two_nsmul, ← one_smul k v, ← add_smul, h2, zero_smul]
    have hfixV : ∀ v : V, (∀ s : S, β s v = v) → v = 0 := fun v hv =>
      eq_zero_of_forall_specialLinear_apply_eq hV fun u => by
        have := hv (β.symm u)
        simpa only [MulEquiv.apply_symm_apply] using this
    have hkerE := mem_fixGL_iff_of_natural (fun s v => β s v) φ heq hker hfixV
    set r := normalizerQuotientHom S φ hφ hkerE with hr
    have hinjS : ∀ s ∈ S, (∀ e, s e - e ∈ fixGL S) → s = 1 := by
      intro s hs h1
      apply congrArg Subtype.val (β.injective (show β ⟨s, hs⟩ = β 1 from ?_))
      rw [map_one]
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      obtain ⟨e, rfl⟩ := hφ v
      have := (hkerE _).1 (h1 e)
      rw [map_sub, sub_eq_zero] at this
      exact (heq ⟨s, hs⟩ e).symm.trans this
    have hNinj := (SteinbergBS.trivial_kernel_extension_normalizer_injection S hES hinjS).2
    have hrinj : Function.Injective r := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      rw [mem_bot]
      refine Subtype.ext (hNinj g g.2 fun e => (hkerE _).2 ?_)
      have := LinearEquiv.congr_fun hg (φ e)
      rw [hr, normalizerQuotientHom_apply] at this
      rw [map_sub, sub_eq_zero]
      exact this
    have hrS : (S.subgroupOf (normalizer (S : Set (E ≃ₗ[ZMod 2] E)))).map r =
        SteinbergCB.specialLinearTwo k V := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨β ⟨g, hg⟩, LinearEquiv.ext fun v => ?_⟩
        obtain ⟨e, rfl⟩ := hφ v
        rw [hr, normalizerQuotientHom_apply]
        exact (heq ⟨g, hg⟩ e).symm
      · rintro ⟨u, rfl⟩
        refine ⟨⟨β.symm u, hSN (β.symm u).2⟩, (β.symm u).2, LinearEquiv.ext fun v => ?_⟩
        obtain ⟨e, rfl⟩ := hφ v
        rw [hr, normalizerQuotientHom_apply]
        have := heq (β.symm u) e
        rw [MulEquiv.apply_symm_apply] at this
        exact this
    have hrH : (H.subgroupOf (normalizer (S : Set (E ≃ₗ[ZMod 2] E)))).map r ≤
        normalizer (SteinbergCB.specialLinearTwo k V : Set (V ≃ₗ[ZMod 2] V)) := by
      rintro _ ⟨g, hg, rfl⟩
      rw [← hrS, mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨g * s * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        simp only [SetLike.mem_coe, mem_subgroupOf] at hs ⊢
        simpa using (mem_normalizer_iff.1 g.2 _).1 hs
      · rintro ⟨s, hs, hsx⟩
        refine ⟨g⁻¹ * s * g, ?_, ?_⟩
        · simp only [SetLike.mem_coe, mem_subgroupOf] at hs ⊢
          have := (mem_normalizer_iff.1 (inv_mem g.2) _).1 hs
          simpa using this
        · rw [map_mul, map_mul, map_inv, hsx]
          group
    obtain ⟨-, hN360, -, -⟩ := SteinbergCB.nq_natural_four_field_normalizer_bound hk hV
    have hHcard : Nat.card H ∣ 360 := by
      have h1 : Nat.card H = Nat.card ((H.subgroupOf
          (normalizer (S : Set (E ≃ₗ[ZMod 2] E)))).map r) := by
        rw [Subgroup.card_map_of_injective hrinj, Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv]
      rw [h1]
      exact (Subgroup.card_dvd_of_le hrH).trans hN360
    have hScard : Nat.card S = 60 := by
      rw [Nat.card_congr β.toEquiv]
      let b := Module.finBasisOfFinrankEq k V hV
      rw [← Nat.card_congr (Matrix.SpecialLinearGroup.toLin_equiv b).toEquiv,
        Matrix.card_SL_field, hk, Fin.prod_univ_two]
      rfl
    have hidx : ¬ 4 ∣ (S.subgroupOf H).index := by
      have h1 : Nat.card H = (S.subgroupOf H).index * 60 := by
        rw [← (S.subgroupOf H).card_mul_index, mul_comm,
          Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hScard]
      rw [h1, show (360 : ℕ) = 6 * 60 by norm_num] at hHcard
      have h6 : (S.subgroupOf H).index ∣ 6 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) hHcard
      intro h4
      have : (4 : ℕ) ∣ 6 := h4.trans h6
      norm_num at this
    have hstab : 4 ∣ Nat.card (MulAction.stabilizer S e) := by
      have : CharP k 2 := by
        have h' : (ringChar k) ∣ 2 := by
          rw [← CharP.cast_eq_zero_iff k (ringChar k), Nat.cast_ofNat, ← one_add_one_eq_two, h2]
        rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1 | h1
        · exact absurd h1 (CharP.ringChar_ne_one)
        · rw [← h1]
          exact ringChar.charP k
      obtain ⟨-, h4⟩ := LieType.nq_natural_central_extension_transvection_stabilizers
        (k := k) (n := 2) le_rfl hV (S.subtype.comp β.symm.toMonoidHom) φ hφ
        (fun u x => by
          have := heq (β.symm u) x
          simp only [MulEquiv.apply_symm_apply] at this
          simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
            using this)
        (fun u x hx => hker _ (β.symm u).2 x hx) e
      obtain ⟨A, hAe, -, hAcard⟩ := h4 (by
        rw [Nat.card_eq_fintype_card, hk]
        norm_num)
      let f : A →* MulAction.stabilizer S e :=
        { toFun := fun a => ⟨β.symm a, by
            rw [MulAction.mem_stabilizer_iff]
            exact hAe a a.2⟩
          map_one' := by ext; simp
          map_mul' := fun a b => by ext; simp }
      have hf : Function.Injective f := fun a b hab => by
        have := congrArg (fun x : MulAction.stabilizer S e => ((x : S) : E ≃ₗ[ZMod 2] E)) hab
        exact Subtype.ext (β.symm.injective (Subtype.ext this))
      rw [← hAcard, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hodd : Odd (Nat.card (MulAction.orbit S e)) := by
      have h1 := card_orbit_mul_card_stabilizer' (G := S) e
      rw [hScard] at h1
      obtain ⟨c, hc⟩ := hstab
      rw [hc] at h1
      have h15 : Nat.card (MulAction.orbit S e) * c = 15 := by
        have h2 : 4 * (Nat.card (MulAction.orbit S e) * c) = 4 * 15 := by
          calc 4 * (Nat.card (MulAction.orbit S e) * c)
              = Nat.card (MulAction.orbit S e) * (4 * c) := by ring
            _ = 4 * 15 := by rw [h1]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
      exact Odd.of_dvd_nat (by decide) ⟨c, h15.symm⟩
    exact not_four_dvd_card_orbit_of_le hSH e hidx hodd
  ·
    obtain ⟨V, _, _, hV, β, φ, hφ, heq, hker⟩ := h
    have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
    have hfixV : ∀ v : V, (∀ s : S, β s v = v) → v = 0 := fun v hv =>
      eq_zero_of_forall_linearEquiv_apply_eq (K := ZMod 2) (by omega) fun u => by
        have := hv (β.symm u)
        simpa only [MulEquiv.apply_symm_apply] using this
    set φ' : E →+ V := φ.toAddMonoidHom with hφ'def
    have hφ' : Function.Surjective φ' := hφ
    have heq' : ∀ (s : S) (e : E), φ' ((s : E ≃ₗ[ZMod 2] E) e) = β s (φ' e) := heq
    have hker' : ∀ s ∈ S, ∀ e : E, φ' e = 0 → s e = e := hker
    have hkerE := mem_fixGL_iff_of_natural (fun s v => β s v) φ' heq' hker' hfixV
    set r := normalizerQuotientHom S φ' hφ' hkerE with hr
    have hinjS : ∀ s ∈ S, (∀ e, s e - e ∈ fixGL S) → s = 1 := by
      intro s hs h1
      apply congrArg Subtype.val (β.injective (show β ⟨s, hs⟩ = β 1 from ?_))
      rw [map_one]
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨e, rfl⟩ := hφ' v
      have := (hkerE _).1 (h1 e)
      rw [map_sub, sub_eq_zero] at this
      exact (heq' ⟨s, hs⟩ e).symm.trans this
    have hNinj := (SteinbergBS.trivial_kernel_extension_normalizer_injection S hES hinjS).2
    have hrS : ∀ g : normalizer (S : Set (E ≃ₗ[ZMod 2] E)), ∃ s, ∃ hs : s ∈ S,
        r g = r ⟨s, hSN hs⟩ := by
      intro g
      refine ⟨β.symm (r g), (β.symm (r g)).2, LinearEquiv.ext fun v => ?_⟩
      obtain ⟨e, rfl⟩ := hφ' v
      rw [hr, normalizerQuotientHom_apply, normalizerQuotientHom_apply]
      have := heq' (β.symm (r g)) e
      rw [MulEquiv.apply_symm_apply] at this
      rw [this, hr, normalizerQuotientHom_apply]
    have hHS : H = S := by
      refine le_antisymm (fun h hh => ?_) hSH
      obtain ⟨s, hs, hrs⟩ := hrS ⟨h, hHN hh⟩
      have h1 : r (⟨s, hSN hs⟩⁻¹ * ⟨h, hHN hh⟩) = 1 := by
        rw [map_mul, map_inv, ← hrs, inv_mul_cancel]
      have h2 : (⟨s, hSN hs⟩ : normalizer (S : Set (E ≃ₗ[ZMod 2] E)))⁻¹ * ⟨h, hHN hh⟩ = 1 := by
        refine Subtype.ext (hNinj _ (mul_mem (inv_mem (hSN hs)) (hHN hh)) fun e => (hkerE _).2 ?_)
        have := LinearEquiv.congr_fun h1 (φ' e)
        rw [hr, normalizerQuotientHom_apply] at this
        rw [map_sub, this]
        exact sub_self _
      have : h = s := by
        have := congrArg Subtype.val h2
        simp only [coe_mul, coe_inv, OneMemClass.coe_one] at this
        exact (inv_mul_eq_one.1 this).symm
      rw [this]
      exact hs
    subst hHS
    have hScard : Nat.card H = 168 := by
      rw [Nat.card_congr β.toEquiv]
      let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
      rw [← Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)).toEquiv,
        Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
      rfl
    have hstab : 4 ∣ Nat.card (MulAction.stabilizer H e) := by
      obtain ⟨-, h4⟩ := LieType.nq_natural_central_extension_transvection_stabilizers
        (k := ZMod 2) (n := 3) (by norm_num) hV
        (H.subtype.comp (β.symm.toMonoidHom.comp SpecialLinearGroup.toLinearEquiv))
        φ' hφ'
        (fun u x => by
          have := heq' (β.symm (SpecialLinearGroup.toLinearEquiv u)) x
          simp only [MulEquiv.apply_symm_apply] at this
          simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
            SpecialLinearGroup.toLinearEquiv_apply] using this)
        (fun u x hx => hker _ (β.symm _).2 x hx) e
      obtain ⟨A, hAe, -, hAcard⟩ := h4 (by rw [Nat.card_zmod]; norm_num)
      let f : A →* MulAction.stabilizer H e :=
        { toFun := fun a => ⟨β.symm (SpecialLinearGroup.toLinearEquiv a), by
            rw [MulAction.mem_stabilizer_iff]
            exact hAe a a.2⟩
          map_one' := by ext; simp
          map_mul' := fun a b => by ext; simp }
      have hf : Function.Injective f := fun a b hab => by
        have := congrArg (fun x : MulAction.stabilizer H e => ((x : H) : E ≃ₗ[ZMod 2] E)) hab
        have h1 := β.symm.injective (Subtype.ext this)
        exact Subtype.ext (SpecialLinearGroup.toLinearEquiv_injective h1)
      rw [← hAcard, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h1 := card_orbit_mul_card_stabilizer' (G := H) e
    rw [hScard] at h1
    obtain ⟨c, hc⟩ := hstab
    rw [hc] at h1
    have h42 : Nat.card (MulAction.orbit H e) * c = 42 := by
      have h2 : 4 * (Nat.card (MulAction.orbit H e) * c) = 4 * 42 := by
        calc 4 * (Nat.card (MulAction.orbit H e) * c)
            = Nat.card (MulAction.orbit H e) * (4 * c) := by ring
          _ = 4 * 42 := by rw [h1]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
    intro h4
    have : (4 : ℕ) ∣ 42 := h4.trans ⟨c, h42.symm⟩
    norm_num at this

end CFSG.Quasithin.H13.NQSetup
