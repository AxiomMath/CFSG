module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixWz

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Centre

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ δ : K ≃+* K}
  (hσ3' : ∀ c, σ (σ (σ c)) = c)

theorem eq_zero_of_trace_fix {a : K} (ha : δ a = a)
    (h : ∀ s : K, δ s = s → a * s + σ (a * s) + σ (σ (a * s)) = 0) : a = 0 := by
  by_contra ha0
  have h1 := h a⁻¹ (by rw [map_inv₀, ha])
  rw [mul_inv_cancel₀ ha0, map_one, map_one] at h1
  have h3 : (1 : K) + 1 + 1 = 1 := by
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)
  rw [h3] at h1
  exact one_ne_zero h1

include hσ3' in
theorem central_Ug_central_Ust {u : Cm σ} (hu : u ∈ Ug σ δ)
    (hcen : ∀ v ∈ Ug σ δ, u * v = v * u) : ∀ x ∈ Ust σ, u * x = x * u := by
  have hσ3 : σ.toRingHom ^ 3 = 1 := toRingHom_pow_three_d4 σ hσ3'
  obtain ⟨a, b, c, d, e, f, hb, he, hf, hu'⟩ :=
    exists_d4coord σ hσ3 (Subgroup.mem_subgroupOf.1 hu.1)
  obtain ⟨ha1, hb1, hc1, hd1, he1, hf1⟩ := (fieldActor_fix_iff σ δ u hu').1 hu.2
  have hcom : ∀ v : Cm σ, v ∈ Ug σ δ → (u : ModGL TwistTag.D4.tag K) * (v : ModGL
      TwistTag.D4.tag K) = (v : ModGL TwistTag.D4.tag K) * (u : ModGL TwistTag.D4.tag K) :=
    fun v hv => congrArg Subtype.val (hcen v hv)
  have h4 : ∀ s : K, δ s = s → a * s + σ (a * s) + σ (σ (a * s)) = 0 ∧
      s * c + σ (s * c) + σ (σ (s * c)) = 0 := by
    intro s hs
    obtain ⟨v, hvU, hv⟩ := exists_Ug_x₄ hσ3 (δ := δ) hs
    have h := conj_eq_of_commute_d4 (hcom v hvU)
    rw [hu', hv, coord_conj_d4x₄ σ hσ3', d4x₄_eq_d4v σ] at h
    have h' := d4v_injective σ h
    exact ⟨h'.2.2.2.1, h'.2.2.2.2⟩
  have ha : a = 0 := eq_zero_of_trace_fix ha1 fun s hs => (h4 s hs).1
  have hc : c = 0 := eq_zero_of_trace_fix hc1 fun s hs => by
    rw [mul_comm]
    exact (h4 s hs).2
  subst ha hc
  rw [d4x₁_zero, one_mul] at hu'
  obtain ⟨v5, hv5U, hv5⟩ := exists_Ug_coord hσ3 (δ := δ) (a := 0) (b := 0) (c := 0) (d := 0)
    (e := 1) (f := 0) (map_zero σ) (map_one σ) (map_zero σ)
    ⟨map_zero δ, map_zero δ, map_zero δ, map_zero δ, map_one δ, map_zero δ⟩
  rw [d4x₁_zero, one_mul] at hv5
  have h5 := hcom v5 hv5U
  rw [hu', hv5] at h5
  have hb0 := d4v_commute_imp σ hσ3' h5
  simp only [mul_zero, map_zero, add_zero, zero_add, one_mul] at hb0
  obtain ⟨v2, hv2U, hv2⟩ := exists_Ug_coord hσ3 (δ := δ) (a := 0) (b := 1) (c := 0) (d := 0)
    (e := 0) (f := 0) (map_one σ) (map_zero σ) (map_zero σ)
    ⟨map_zero δ, map_one δ, map_zero δ, map_zero δ, map_zero δ, map_zero δ⟩
  rw [d4x₁_zero, one_mul] at hv2
  have h2 := hcom v2 hv2U
  rw [hu', hv2] at h2
  have he0 := d4v_commute_imp σ hσ3' h2
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, mul_one] at he0
  have hd0 : d = 0 := eq_zero_of_trace_fix hd1 fun γ hγ => by
    obtain ⟨v3, hv3U, hv3⟩ := exists_Ug_x₃ hσ3 (δ := δ) hγ
    have h3 := hcom v3 hv3U
    rw [hu', hv3, d4x₃_eq_d4v σ] at h3
    have h' := d4v_commute_imp σ hσ3' h3
    simpa using h'
  have hbe : (u : ModGL TwistTag.D4.tag K) = d4x₆ K f := by
    rw [hu', ← hb0, hd0, he0, ← d4x₆_eq_d4v σ]
  intro x hx
  refine Subtype.ext ?_
  have hx' : (x : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := Subgroup.mem_subgroupOf.1 hx
  have := commute_d4x₆_of_mem σ hσ3' hx' f
  show (u : ModGL TwistTag.D4.tag K) * (x : ModGL TwistTag.D4.tag K) =
    (x : ModGL TwistTag.D4.tag K) * (u : ModGL TwistTag.D4.tag K)
  rw [hbe]
  exact this.symm

end Centre

section Wle

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {f e : ℕ} (hf : 1 ≤ f) (hfe : f = 2 * e)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hfe hK hσ in
theorem Wg_le_centerOf {S2 : Subgroup (K ≃+* K)} {T S : Subgroup (MulAut (Cm σ))}
    (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S2, α = MulAut.conj u *
      fieldActor σ δ')
    (hS : ∀ α : MulAut (Cm σ), α ∈ S ↔ ∃ u ∈ Ust σ, MulAut.conj u = α) :
    centerOf (Tg σ δ T) ⊓ ⁅Tg σ δ T, Tg σ δ T⁆ ≤ centerOf S := by
  have hf' := hf
  subst hfe
  have he : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (6 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK6
  have hσ3' : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hK hσ
  rintro w ⟨⟨hwT, hwc⟩, hwK⟩
  have hker : w ∈ (theta σ hf' hK hσ).ker := by
    have h : ⁅Tg σ δ T, Tg σ δ T⁆ ≤ (theta σ hf' hK hσ).ker := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact RingEquiv.ext fun c => ringEquiv_comm_of_finite _ _ c
    exact h hwK
  obtain ⟨u, hu, δ', hδ', rfl⟩ := (mem_Tg_iff σ δ hT w).1 hwT
  have hδ1 : δ' = 1 := by
    have h1 := hker
    rw [MonoidHom.mem_ker, theta_conj_fieldActor] at h1
    exact h1
  subst hδ1
  rw [fieldActor_one, mul_one] at hwc hwT ⊢
  have hcen : ∀ v ∈ Ug σ δ, u * v = v * u := by
    intro v hv
    have hvT : MulAut.conj v ∈ Tg σ δ T :=
      (mem_Tg_iff σ δ hT _).2 ⟨v, hv, 1, S2.one_mem, by rw [fieldActor_one, mul_one]⟩
    have h1 := (Subgroup.mem_centralizer_iff.1 hwc) _ hvT
    exact conj_injective σ (by rw [map_mul, map_mul]; exact h1.symm)
  have hcs := central_Ug_central_Ust hσ3' hu hcen
  refine ⟨(hS _).2 ⟨u, hu.1, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro α hα
  obtain ⟨x, hx, rfl⟩ := (hS α).1 hα
  rw [← map_mul, ← map_mul, hcs x hx]

end Wle


end CFSG.Quasithin.H13.F431.D4q.Out
