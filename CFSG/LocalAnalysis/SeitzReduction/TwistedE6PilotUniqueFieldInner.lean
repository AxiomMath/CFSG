module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

theorem one_le_of_card_sq_twistedE6 {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | h
  · have : Finite K := finite_of_card hK
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    norm_num at h1
  · exact h

theorem card_eq_two_pow_two_mul_twistedE6 {f : ℕ} {K : Type} (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card K = 2 ^ (2 * f) := by
  rw [hK, ← pow_mul, mul_comm]

section Generic

variable {G : Type} [Group G] [Finite G]

theorem not_inner_quot_of_two_pow_dvd_centralizer {t : G} (ht : orderOf t = 2) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {C : Type*} [Group C]
    (eM : M ⧸ center M ≃* C) (htM : t ∈ normalizer (M : Set G)) {u : C} (hu : orderOf u = 2)
    {a : ℕ} (hA : ∀ w : C, orderOf w = 2 → 2 ^ a ∣ Nat.card (centralizer ({w} : Set C)))
    (hB : ¬ 2 ^ a ∣ Nat.card (centralizer ({t} : Set G))) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉ (MulAut.conj : C →* MulAut C).range := by
  rintro ⟨c, hc⟩
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := E6Pilot.eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := E6Pilot.normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [E6Pilot.mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := E6Pilot.odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : C := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set C) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := E6Pilot.exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [E6Pilot.mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  refine hB ((hA _ hŵ).trans ?_)
  refine (card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [← card_map_of_injective M.subtype_injective]
  exact card_dvd_of_le hleG

end Generic

section TwoParts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem factorization_card_le_of_le_centralizer_twistedE6 (hL : standardComponentIsStandard L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) :
    (Nat.card X).factorization 2 ≤ 36 * f + 2 + f.factorization 2 := by
  have hf := one_le_of_card_sq_twistedE6 hK
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) := MulEquiv.finite_left
  have h1 := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer hL e ht hKt hXt
  have h2 := factorization_two_mul_card_mulAut_twistedE6_le hf hK hσ
  have hA0 : 2 * Nat.card (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) ≠ 0 :=
    mul_ne_zero two_ne_zero Nat.card_pos.ne'
  exact ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' hA0).2 h1 2).trans h2

theorem not_two_pow_dvd_card_centralizer_twistedE6 (hL : standardComponentIsStandard L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ¬ 2 ^ (26 * (2 * f)) ∣ Nat.card (centralizer ({t} : Set G)) := by
  intro hdvd
  have hf := one_le_of_card_sq_twistedE6 hK
  have hb := factorization_card_le_of_le_centralizer_twistedE6 hL hK hσ e ht hKt
    (le_refl (centralizer ({t} : Set G)))
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega

end TwoParts

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_twistedE6 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
  have hK₂' := card_eq_two_pow_two_mul_twistedE6 hK₂
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂'
  exact not_inner_quot_of_two_pow_dvd_centralizer ht hMp hZ eM htM
    (E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1))
    (a := 26 * (2 * f)) (fun w hw => E6Pilot.two_pow_dvd_card_centralizer_E6 hK₂' hw)
    (not_two_pow_dvd_card_centralizer_twistedE6 hset.standard hK hσ e ht hKt)

end Inner

end CFSG.SeitzReduction.TwistedE6Pilot
