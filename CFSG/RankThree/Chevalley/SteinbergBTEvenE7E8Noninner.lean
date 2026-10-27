module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8AllOrders

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  SteinbergBT

theorem even_E7_E8_noninner_prime_field_descent_and_local_core_trivial (τ : Tag)
    (hτ : τ = .E7 ∨ τ = .E8) {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (B : Subgroup (MulAut (adjointGroup τ K)))
    (hB : (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup τ K)) ∉
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hαp : orderOf α = p) (x : adjointGroup τ K) (σ : K ≃+* K)
    (hxσ : (α : MulAut (adjointGroup τ K)) = MulAut.conj x * entrywiseAdjointAut τ σ) :
    orderOf σ = p ∧ p ∣ f ∧
      (∃ ψ : MulAut (adjointGroup τ K),
        ψ * (α : MulAut (adjointGroup τ K)) * ψ⁻¹ = entrywiseAdjointAut τ σ) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  set α' : MulAut (adjointGroup τ K) := (α : MulAut (adjointGroup τ K)) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  obtain ⟨-, Θ, hΘ, -, hΘker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  have hΘα : Θ α' = σ := hΘ α' x σ fun h => by
    rw [hxσ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  have hσp : orderOf σ = p := by
    have h1 : σ ^ p = 1 := by rw [← hΘα, ← map_pow, hα'pow, map_one]
    have h2 : σ ≠ 1 := fun h1 => hα (by rw [← hΘker, MonoidHom.mem_ker, hΘα, h1])
    exact orderOf_eq_prime h1 h2
  obtain ⟨hpf, -⟩ := card_fixSubfield Nat.prime_two hf hK σ
  rw [hσp] at hpf
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hσmem : σ ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top σ
  obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hkσ : fr ^ k = σ := hkσ
  rw [Finset.mem_range, hord] at hk
  have hdk : d ∣ k := by
    have h1 : f ∣ k * p := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkσ, ← hσp, pow_orderOf_eq_one]
    rw [← hdp] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  obtain ⟨j, rfl⟩ := hdk
  have hjp : j < p := by
    by_contra hjp
    have : d * p ≤ d * j := Nat.mul_le_mul_left d (not_lt.1 hjp)
    omega
  have hj0 : 0 < j := by
    refine Nat.pos_of_ne_zero fun hj => ?_
    rw [hj, mul_zero, pow_zero] at hkσ
    rw [← hkσ, orderOf_one] at hσp
    exact hp.one_lt.ne hσp
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ (2 ^ d) := ringAut_pow_apply_of_frobenius hfr d
  have hTj : T ^ j = σ := by rw [hTdef, ← pow_mul, hkσ]
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  have hσr : σ ^ r = T := by
    rw [← hTj, ← pow_mul, pow_eq_self_of_mod_eq_one hTord (by rw [mul_comm]; exact hr)]
  have hβ : α' ^ r = MulAut.conj (((List.range r).map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ T := by
    rw [hxσ, conj_mul_pow, ← entrywiseAdjointAut_pow, hσr]
  have hβp : (MulAut.conj (((List.range r).map fun i =>
      (entrywiseAdjointAut τ σ ^ i) x).prod) * entrywiseAdjointAut τ T) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut τ K hK hd0 hp.one_lt.le hdp T hT
    (AlgebraicClosure K) _ hβp
  have hψα : ψ * α' * ψ⁻¹ = entrywiseAdjointAut τ σ := by
    have hαβ : α' = (α' ^ r) ^ j := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hr]
    rw [hαβ, ← conj_pow, hβ, hψ, ← entrywiseAdjointAut_pow, hTj]
  obtain ⟨-, hJC, hsimple, hnc, ⟨ι, -⟩, -, -, hNδ, hnormal, hcent, -⟩ :=
    even_E7_E8_canonical_field_centralizer_all_orders τ hτ hf K hK σ
  exact ⟨hσp, ⟨d, hd⟩, ⟨ψ, hψα⟩, aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α
    hαp ψ _ hψα hsimple hnc ι hNδ hnormal hcent⟩

end CFSG.RankThree.Chevalley
