module

public import CFSG.RankThree.Chevalley.SteinbergCFOddE7NoninnerCore
public import CFSG.RankThree.PartOne.KE.OddE6NoninnerOuter
public import CFSG.RankThree.PartOne.KE.OddE6Rational

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.RankThree.Chevalley (exists_conj_eq_entrywiseAdjointAut_of_orderOf
  odd_entrywise_canonical_core_data_of_fixer aschbacherSolvableCore_centralizer_eq_bot_of_inner)

theorem odd_E6_noninner_large_prime_field_descent_and_local_core_trivial {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (adjointGroup .E6 K)))
    (hB : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup .E6 K)) ∉
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range)
    (hαp : orderOf α = p) :
    p ∣ f ∧
    (∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup .E6 K)), orderOf σ = p ∧
      δ * (α : MulAut (adjointGroup .E6 K)) * δ⁻¹ = entrywiseAdjointAut .E6 σ) ∧
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, -, ρ, -, -, -, hDnormal, hidx, -, -, -, hNF, ⟨π, -, -, hπ⟩, -, hfixer⟩ :=
    odd_E6_rational_inner_diagonal_graph_field_automorphism_structure hℓ hℓ2 hf K hK
      (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
  have hα'p : orderOf (α : MulAut (adjointGroup .E6 K)) = p := by
    rw [Subgroup.orderOf_coe, hαp]
  have hαpow : (α : MulAut (adjointGroup .E6 K)) ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one _
  obtain ⟨⟨z, ε, σ⟩, hzσ, -⟩ := hNF α
  simp only at hzσ
  have hπα : π (α : MulAut (adjointGroup .E6 K)) = (ε, σ) := by
    rw [hzσ]
    exact hπ z (ε, σ)
  obtain ⟨hεp, hσp1⟩ : ε ^ p = 1 ∧ σ ^ p = 1 := by
    have h1 := congrArg π hαpow
    rw [map_pow, hπα, map_one, Prod.pow_mk, Prod.mk_eq_one] at h1
    exact h1
  have hε2 : ∀ e : Multiplicative (ZMod 2), e ^ 2 = 1 := by decide
  have hε : ε = 1 := by
    have h2 : orderOf ε ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hεp) (orderOf_dvd_of_pow_eq_one (hε2 ε))
    rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2] at h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  subst hε
  have hγ1 : graphFieldHom (K := K) (1, σ) = entrywiseAdjointAut Tag.E6 σ := by
    have h := graphFieldHom_apply (K := K) 0 σ
    rwa [ofAdd_zero, ZMod.val_zero, graphAut_zero, one_mul] at h
  rw [hγ1] at hzσ
  have hzinn := mem_inner_of_pow_mul_eq_one_of_index_dvd_three hidx hp hp3 ⟨z, rfl⟩
    (by rw [← entrywiseAdjointAut_pow, hσp1, entrywiseAdjointAut_one]) (hzσ ▸ hαpow)
  obtain ⟨x, hx⟩ : ρ z ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
    hzinn
  rw [← hx] at hzσ
  have hσp : orderOf σ = p := by
    refine orderOf_eq_prime hσp1 fun h => hα ?_
    rw [hzσ, h, entrywiseAdjointAut_one, mul_one]
    exact ⟨x, rfl⟩
  obtain ⟨hpf, δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_orderOf .E6 hℓ hf K hK hp x σ hσp
    (by rw [← hzσ]; exact hα'p)
  rw [← hzσ] at hδ
  refine ⟨hpf, ⟨σ, δ, hσp, hδ⟩, ?_⟩
  have hfixer' : ∀ β : MulAut (adjointGroup .E6 K),
      (∀ j : adjointGroup .E6 K, (j : ModGL .E6 K) ∈ fixedFieldImage .E6 σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut .E6 η := by
    intro β hβ
    have hS := (hfixer (fixSubfield σ) _ rfl).1
    have hβS : β ∈ ((fixingSubgroup (MulAut (adjointGroup Tag.E6 K))
        {j : adjointGroup Tag.E6 K | (j : ModGL Tag.E6 K) ∈
          (adjointGroup Tag.E6 (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)} :
            Subgroup (MulAut (adjointGroup Tag.E6 K))) : Set (MulAut (adjointGroup Tag.E6 K))) :=
      (mem_fixingSubgroup_iff _).2 fun j hj => hβ j hj
    rw [hS] at hβS
    obtain ⟨σ', rfl⟩ := hβS
    refine ⟨σ'.toRingEquiv, fun c hc => ?_, rfl⟩
    have h1 := σ'.commutes (⟨c, hc⟩ : fixSubfield σ)
    exact h1
  obtain ⟨hJC, hsimple, hnc, ⟨ι⟩, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data_of_fixer (τ := .E6) hℓ2 σ hfixer'
  exact aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α hαp δ _ hδ hsimple hnc ι
    hNδ hnormal hcent

end CFSG.RankThree.PartOne.KE
