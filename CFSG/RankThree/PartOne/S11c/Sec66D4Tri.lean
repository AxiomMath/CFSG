module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

theorem lieModel_graphFixedRootGroup_trialityD4
    {d : ℕ} (hd : 1 ≤ d) {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ d) ^ 3)
    (σ₀ : k ≃+* k) (hσ₀ : (∀ c, σ₀ c = c ^ 2 ^ d) ∨ ∀ c, σ₀ c = c ^ (2 ^ d) ^ 2) :
    LieModel ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) .trialityD4 0 2 d := by
  have : Fintype k := Fintype.ofFinite k
  have hq3 : ∀ c : k, c ^ (2 ^ d) ^ 3 = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨σ₁, hσ₁, ⟨e₁⟩⟩ : ∃ σ₁ : k ≃+* k, (∀ c, σ₁ c = c ^ 2 ^ d) ∧
      Nonempty (↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom)) := by
    rcases hσ₀ with h | h
    · exact ⟨σ₀, h, ⟨MulEquiv.refl _⟩⟩
    · refine ⟨σ₀.symm, fun c => ?_, ?_⟩
      · refine σ₀.symm_apply_eq.2 ?_
        rw [h, ← pow_mul, show 2 ^ d * (2 ^ d) ^ 2 = (2 ^ d) ^ 3 by ring, hq3]
      · obtain ⟨f, -⟩ := exists_mulEquiv_of_map_eq (trialityTranspositionAut k)
          (map_trialityTranspositionAut_graphFixedRootGroup σ₀)
        exact ⟨f⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨eDQ⟩⟩ := even_triality_exact_automorphism_normal_form hd k hk σ₁ hσ₁
  exact lieModel_trialityD4_iff.mpr ⟨rfl, ⟨Nat.prime_two, hd, rfl⟩, k, inferInstance,
    inferInstance, hk, σ₁.toRingHom, hσ₁, ⟨e₁.trans eDQ.symm⟩⟩

theorem sec66T_K2_trialityD4 :
    Sec66T_K2 .trialityD4 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨-, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hKcard σ hσ
  refine no_plane_of_cyclic_quotient hp (Θ.comp (MulAut.congr e).toMonoidHom) ?_ E hE hcard hEinn
  intro x hx _
  have hmem : MulAut.congr e x ∈ Θ.ker := hx
  rw [hker] at hmem
  exact (mem_innerAut_congr e x).mp hmem

theorem sec66T_K1_trialityD4 :
    Sec66T_K1 .trialityD4 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  obtain ⟨hn0, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  subst hn0
  have hf : 1 ≤ f := hadmf.2.1
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ f) ^ 3 := hKcard
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv T e.toEquiv
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e α
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := one_le_of_mul_eq hf hff'
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α') = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α')) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α')) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixSub (MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹) =
      fixSub (fieldActor σ δc) := by
    have h1 : MulAut.conj h₀ * MulAut.congr e α * (MulAut.conj h₀)⁻¹ = fieldActor σ (Θ α') := hh₀
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.D4) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (3 * f' * p) := by rw [hK3, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨-, -, hk, hres, -, -, hfixJ, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hd hp.two_le hm3
      K hK' σ hσ' δc hδc
  have : Finite (fixSubfield δc) := Subtype.finite
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  set J := trialityFieldImage σ δc
  let e3 : ↥(fixSub (fieldActor σ δc)) ≃* ↥J :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hK0 : Nat.card (fixSubfield δc) = (2 ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hcardK0 : Fintype.card (fixSubfield δc) = 2 ^ (3 * f') := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  obtain ⟨j, r, hr, hpjr⟩ : ∃ j r : ℕ, (r = 1 ∨ r = 2) ∧ p = 3 * j + r := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
    · exact ⟨p / 3, 1, Or.inl rfl, by omega⟩
    · exact ⟨p / 3, 2, Or.inr rfl, by omega⟩
  have hpowj : ∀ c : fixSubfield δc, c ^ (2 ^ (3 * f')) ^ j = c := fun c => by
    have h := FiniteField.pow_card_pow j c
    rwa [hcardK0] at h
  have hσ0pow' : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ (f' * r) := fun c => by
    have h2 : 2 ^ (f' * p) = (2 ^ (3 * f')) ^ j * 2 ^ (f' * r) := by
      rw [hpjr]
      ring
    rw [hσ0pow c, h2, pow_mul, hpowj c]
  have hσ0orient : (∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ 2 ^ f') ∨
      ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ (2 ^ f') ^ 2 := by
    rcases hr with rfl | rfl
    · exact Or.inl fun c => by rw [hσ0pow' c, mul_one]
    · exact Or.inr fun c => by rw [hσ0pow' c, ← pow_mul]
  have hXmodel : LieModel ↥J .trialityD4 0 2 f' :=
    lieModel_of_mulEquiv
      ((graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
        (fixSubfieldRestrict σ δc).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _))
      (lieModel_graphFixedRootGroup_trialityD4 hd hK0 (fixSubfieldRestrict σ δc) hσ0orient)
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have := hsimple
  have hfix : LieModel (↥(fixRes (fieldActor σ δc)) ⧸ Subgroup.center ↥(fixRes (fieldActor σ δc)))
      .trialityD4 0 2 f' := lieModel_fixRes_of_simple hnc' e3 hXmodel
  exact fieldAutT_of_conj_fix' e hM hff' hd α (fieldActor σ δc) (MulAut.conj h₀) hfix_eq hfix

end CFSG.RankThree.PartOne.Sec66T
