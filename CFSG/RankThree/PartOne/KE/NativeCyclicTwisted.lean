module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.RankThree.PartOne.KE.EndpointStatements
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innerSubgroup
open CFSG.LieType.Chevalley

theorem twistedE6_outer_commutator_odd {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ¬ 2 ∣ Nat.card (commutator (Outer (twistedE6RootGroup K σ))) := by
  classical
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hℓ K hK').2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hle : innerSubgroup (twistedE6RootGroup K σ) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  set Φ := QuotientGroup.lift (innerSubgroup (twistedE6RootGroup K σ)) Θ hle
  have hcube' : ∀ x ∈ Φ.ker, x ^ 3 = 1 := by
    intro x hx
    rw [QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  have : Finite (Outer (twistedE6RootGroup K σ)) := by
    have : Finite (MulAut (twistedE6RootGroup K σ)) := MulEquiv.finite_left
    infer_instance
  have hodd : Odd (Nat.card Φ.ker) := by
    rw [Nat.odd_iff]
    by_contra h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Φ.ker) 2 (by omega)
    have h3 : x ^ 3 = 1 := Subtype.ext (by simpa using hcube' x x.2)
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hx] at h4
    omega
  have hab : ∀ a b : RingAut K, a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := RingAut K)).is_comm.comm a b
  have hc : commutator (Outer (twistedE6RootGroup K σ)) ≤ Φ.ker := commutator_le_ker_of_comm Φ hab
  have hdvd := Subgroup.card_dvd_of_le hc
  intro h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))

theorem localCoreTrivialOn_noninner_twistedE6 {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (twistedE6RootGroup K σ) =>
      α ∉ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
    (twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK' σ hσ Θ hΘ
      hp hp3 B hB α hα hαp).2.2.2

theorem planeLocalCoreOdd_twistedE6_of_cyclic {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcyc : ∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : twistedE6RootGroup K σ, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    PlaneLocalCoreOdd p (twistedE6RootGroup K σ) := by
  have : Finite (ModGL TwistTag.E6.tag K) := CFSG.LieType.Chevalley.finite_modGL
  exact planeLocalCoreOdd_of_cyclic_centralizers_abstract hp hp3
    (exceptional_fixed_center_trivial TwistTag.E6 K σ) hcyc hcent
    (twistedE6_outer_commutator_odd hℓ hf hK σ hσ)
    (localCoreTrivialOn_noninner_twistedE6 hℓ hf hK σ hσ hp hp3)

theorem oddEndpoint_twistedE6_of_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p ℓ f : ℕ), p.Prime → 3 < p →
      ℓ.Prime → ℓ ≠ p → 1 ≤ f → Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
      Cond p ℓ f →
      (∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q) ∧
        ∀ x : twistedE6RootGroup K σ, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    OddEndpoint .twistedE6 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  have hm' : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (ℓ ^ f) := hmod.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm'
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  obtain ⟨hcyc, hcent⟩ := h K σ p ℓ f hp hp3 hℓ hℓp hf hK2 hσ hc
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_twistedE6_of_cyclic hℓ hf hK2 σ hσ hp hp3 hcyc hcent)).1

end CFSG.RankThree.PartOne.KE
