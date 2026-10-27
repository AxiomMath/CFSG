module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem exists_canonical_generator_odd {K : Type} [Field K] {f p f' : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ (2 * f)) {η : K ≃+* K} (hη : orderOf η = p) (hp : p.Prime)
    (hp2 : p ≠ 2) (hff' : f = p * f') :
    ∃ ε : K ≃+* K, (∀ c, ε c = c ^ 2 ^ (f' * (p + 1))) ∧
      Subgroup.zpowers η = Subgroup.zpowers ε := by
  obtain ⟨φ, hφ, hφord, hgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * f) hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hgen⟩
  have hf'pos : 1 ≤ f' := one_le_of_mul_eq hf hff'
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine ⟨φ ^ (f' * (p + 1)), ringAut_pow_apply_of_frobenius hφ _, ?_⟩
  have hεp : (φ ^ (f' * (p + 1))) ^ p = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hφord]
    exact ⟨j + 1, by rw [hff', hj]; ring⟩
  have hε1 : φ ^ (f' * (p + 1)) ≠ 1 := by
    intro h
    rw [← orderOf_dvd_iff_pow_eq_one, hφord, hff'] at h
    have h2 := Nat.le_of_dvd (by positivity) h
    nlinarith
  have : Fact p.Prime := ⟨hp⟩
  have hεord : orderOf (φ ^ (f' * (p + 1))) = p := orderOf_eq_prime hεp hε1
  have h1 : Nat.card (Subgroup.zpowers η) = p := by rw [Nat.card_zpowers, hη]
  have h2 : Nat.card (Subgroup.zpowers (φ ^ (f' * (p + 1)))) = p := by
    rw [Nat.card_zpowers, hεord]
  have : Finite (Subgroup.zpowers η) := Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
  have : Finite (Subgroup.zpowers (φ ^ (f' * (p + 1)))) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
  exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)

theorem sec66T_K2_twistedE6 :
    Sec66T_K2 .twistedE6 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨-, hCEM⟩ := lieModel_twistedE6_iff.mp hM
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hCEM
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hKcard, ← pow_mul, mul_comm]
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut (by omega) hK2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hKcard σ hσ
  refine no_plane_of_cyclic_quotient hp (Θ.comp (MulAut.congr e).toMonoidHom) ?_ E hE hcard hEinn
  intro x hx hxp
  have hmem : MulAut.congr e x ∈ Θ.ker := hx
  rw [hker] at hmem
  set H := twistedE6Inn K σ ⊔ twistedE6Diag K σ
  set a := QuotientGroup.mk' ((twistedE6Inn K σ).subgroupOf H) (⟨MulAut.congr e x, hmem⟩ : H)
    with ha
  have hxp' : (⟨MulAut.congr e x, hmem⟩ : H) ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← map_pow, hxp, map_one]
    rfl)
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp', map_one]
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hap) (orderOf_dvd_of_pow_eq_one (hcube a))))
  have h2 := (QuotientGroup.eq_one_iff (N := (twistedE6Inn K σ).subgroupOf H) _).1 ha1
  rw [Subgroup.mem_subgroupOf] at h2
  exact (mem_innerAut_congr e x).mp h2

theorem sec66T_K1_twistedE6 :
    Sec66T_K1 .twistedE6 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  obtain ⟨hn0, hCEM⟩ := lieModel_twistedE6_iff.mp hM
  subst hn0
  have hf : 1 ≤ f := hadmf.2.1
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hCEM
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hKcard, ← pow_mul, mul_comm]
  have : Finite (twistedE6RootGroup K σ) := Finite.of_equiv T e.toEquiv
  set α' : MulAut (twistedE6RootGroup K σ) := MulAut.congr e α
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hKcard σ hσ
  obtain ⟨hηord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK2 σ
      hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := one_le_of_mul_eq hf hff'
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ε, hε, hzp⟩ := exists_canonical_generator_odd hf hK2 hηord hp hp2 hff'
  have hfix_eq : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub (fieldActor σ ε) := by
    have h1 : ψ * MulAut.congr e α * ψ⁻¹ = fieldActor σ (Θ α') := hψ
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.E6) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (2 * f' * p) := by rw [hK2, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨φ, hφ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * f) hK2
  obtain ⟨κ, hκdef⟩ : ∃ κ, φ ^ (2 * f') = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * f') := fun c => by
    rw [← hκdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  obtain ⟨T, hTdef⟩ : ∃ T, φ ^ f' = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ 2 ^ f' := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  set σ₀ : fixSubfield κ ≃+* fixSubfield κ := fixSubfieldRestrict T κ with hσ₀def
  have hσ₀ : ∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f' := fun c => by
    rw [hσ₀def, coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hk, hJC, -, hder, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd
      (by omega : 3 ≤ p) (hp.odd_of_ne_two hp2) K hK' κ hκ σ hσ' σ₀ hσ₀ ε hε
  have : Finite (fixSubfield κ) := Subtype.finite
  set Γ : Subgroup (twistedE6RootGroup K σ) := fixSub (fieldActor σ ε)
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀
  set N : Subgroup (twistedE6RootGroup K σ) := J.subgroupOf (twistedE6RootGroup K σ)
  have hder' : ⁅Γ, Γ⁆ = N := hder
  have hNsub : N.subgroupOf Γ = commutator ↥Γ := by
    rw [← hder', ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hNΓ : N ≤ Γ := hder' ▸ Subgroup.commutator_le_self Γ
  have hNnormal : (N.subgroupOf Γ).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥Γ ⧸ N.subgroupOf Γ) := by
    have : (N.subgroupOf Γ).Normal := hNnormal
    have : CommGroup (↥Γ ⧸ commutator ↥Γ) := inferInstanceAs (CommGroup (Abelianization ↥Γ))
    have : Group.IsSolvable (↥Γ ⧸ commutator ↥Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have hJperf : Group.IsPerfect ↥J := by
    have := hsimple
    exact isPerfect_of_simple_nonabelian hnc'
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).symm.surjective
  have hZk : Subgroup.center (twistedE6RootGroup (fixSubfield κ) σ₀) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 (fixSubfield κ) σ₀
  let eJ : ↥J ≃* twistedE6RootGroup (fixSubfield κ) σ₀ :=
    (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)).symm
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* twistedE6RootGroup (fixSubfield κ) σ₀ :=
    (centerQuotientCongr ((Subgroup.subgroupOfEquivOfLe hJC).trans eJ)).trans
      (centerQuotientEquivSelf hZk)
  have hK0 : Nat.card (fixSubfield κ) = (2 ^ f') ^ 2 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ 2 ^ f' := fun c => Subtype.ext (by
    rw [hσ₀, SubmonoidClass.coe_pow])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eDQ⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hd (fixSubfield κ)
      hK0 σ₀ hσ₀'
  have hXmodel : LieModel (twistedE6RootGroup (fixSubfield κ) σ₀) .twistedE6 0 2 f' :=
    lieModel_twistedE6_iff.mpr ⟨rfl, ⟨Nat.prime_two, hd, rfl⟩, fixSubfield κ, inferInstance,
      inferInstance, hK0, σ₀.toRingHom, hσ₀', ⟨eDQ.symm⟩⟩
  have hfix : LieModel (↥(fixRes (fieldActor σ ε)) ⧸ Subgroup.center ↥(fixRes (fieldActor σ ε)))
      .twistedE6 0 2 f' :=
    lieModel_fixRes_of_normal hNΓ hNnormal hNperf hsolv eN hXmodel
  exact fieldAutT_of_conj_fix' e hM hff' hd α (fieldActor σ ε) ψ hfix_eq hfix

end CFSG.RankThree.PartOne.Sec66T
