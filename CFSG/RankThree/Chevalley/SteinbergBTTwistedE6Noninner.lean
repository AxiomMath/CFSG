module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B)
    (α : B) (hα : (α : MulAut (twistedE6RootGroup K σ)) ∉
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range)
    (hαp : orderOf α = p) :
    orderOf (Θ α) = p ∧ p ∣ f ∧
      (∃ ψ : MulAut (twistedE6RootGroup K σ),
        ψ * (α : MulAut (twistedE6RootGroup K σ)) * ψ⁻¹ = fieldActor σ (Θ α)) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  set α' : MulAut (twistedE6RootGroup K σ) := (α : MulAut (twistedE6RootGroup K σ)) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  obtain ⟨η, hηdef⟩ : ∃ η, Θ α' = η := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hex, ⟨Θ', hΘ', -, hker', -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK2 σ hσ
  have hΘΘ' : ∀ β, Θ β = Θ' β := fun β => by
    obtain ⟨g, u, δ, hβ⟩ := hex β
    rw [hΘ β g u δ hβ, hΘ' β g u δ hβ]
  have hηp : η ^ p = 1 := by rw [← hηdef, ← map_pow, hα'pow, map_one]
  have hη1 : η ≠ 1 := by
    intro h1
    have hmem : α' ∈ Θ'.ker := by rw [MonoidHom.mem_ker, ← hΘΘ', hηdef, h1]
    rw [hker'] at hmem
    set H := twistedE6Inn K σ ⊔ twistedE6Diag K σ
    set a := QuotientGroup.mk' ((twistedE6Inn K σ).subgroupOf H) (⟨α', hmem⟩ : H) with ha
    have hxp : (⟨α', hmem⟩ : H) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hα'pow)
    have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp, map_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hap) (orderOf_dvd_of_pow_eq_one (hcube a))))
    have h2 := (QuotientGroup.eq_one_iff (N := (twistedE6Inn K σ).subgroupOf H) _).1 ha1
    rw [Subgroup.mem_subgroupOf] at h2
    exact hα h2
  have hηo : orderOf η = p := orderOf_eq_prime hηp hη1
  obtain ⟨d, hd, hd0, r, s, T, ε, hT, hε, hαβ, ψ, hψ, hψα⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp (by omega) α' hα'pow (by rw [hηdef]; exact hη1)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hαβB : (α ^ r) ^ s = α :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow]; exact hαβ)
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, ← pow_add, two_mul]
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK, ← hdp, mul_assoc]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp, hσ]
  obtain ⟨-, -, hJC, -, -, hsimple, hnc, ⟨ιN, -⟩, hNδ, hnormal, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd0
      (by omega : 3 ≤ p) (hp.odd_of_ne_two (by omega)) K hKdp κ hκ σ hσdp
      (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hαr : orderOf (α ^ r) = p := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← pow_mul, mul_comm, pow_mul, ← hαp, pow_orderOf_eq_one, one_pow]
    · have h2 : α = 1 := by rw [← hαβB, h1, one_pow]
      rw [h2, orderOf_one] at hαp
      exact hp.one_lt.ne hαp
  have hcentr : (Subgroup.centralizer {α} : Subgroup B) = Subgroup.centralizer {α ^ r} := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ((Commute.pow_right h r).eq : _)
    · intro h
      have h1 := (Commute.pow_right (show Commute y (α ^ r) from h) s).eq
      rwa [hαβB] at h1
  have hψr : ψ * ((α ^ r : B) : MulAut (twistedE6RootGroup K σ)) * ψ⁻¹ = fieldActor σ ε := by
    rw [Subgroup.coe_pow]
    exact hψ
  refine ⟨by rw [hηdef]; exact hηo, ⟨d, hd⟩, ⟨ψ, hψα⟩, ?_⟩
  rw [hcentr]
  exact aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB (α ^ r) hαr ψ _ hψr
    hsimple hnc ιN hNδ hnormal hcent

end CFSG.RankThree.Chevalley
