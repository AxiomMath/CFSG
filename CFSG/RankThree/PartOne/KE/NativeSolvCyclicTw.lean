module

public import CFSG.RankThree.PartOne.KE.NativeSolvCyclic
public import CFSG.RankThree.PartOne.KE.NativeCyclicTwisted

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Chevalley

theorem four_le_pow_of_noninner_twistedE6 {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hex : ∃ α : MulAut (twistedE6RootGroup K σ),
      α ∉ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ∧
        orderOf α = p) :
    4 ≤ ℓ ^ f := by
  obtain ⟨α, hα, hαp⟩ := hex
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hαB : orderOf (⟨α, Subgroup.mem_top α⟩ :
      (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ)))) = p := by
    rw [Subgroup.orderOf_mk, hαp]
  have hdvd := (twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK'
    σ hσ Θ hΘ hp hp3 ⊤ le_top ⟨α, Subgroup.mem_top α⟩ hα hαB).2.1
  have hpf : p ≤ f := Nat.le_of_dvd (by omega) hdvd
  calc 4 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hpf
    _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f

theorem planeLocalCoreOdd_twistedE6_of_solvable_cyclic {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcyc : ∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q)
    (hcent : 4 ≤ ℓ ^ f → ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V → IsCyclic V) :
    PlaneLocalCoreOdd p (twistedE6RootGroup K σ) := by
  have : Finite (ModGL TwistTag.E6.tag K) := CFSG.LieType.Chevalley.finite_modGL
  exact planeLocalCoreOdd_of_solvable_cyclic_abstract hp hp3
    (exceptional_fixed_center_trivial TwistTag.E6 K σ) hcyc
    (fun hex => hcent (four_le_pow_of_noninner_twistedE6 hℓ hf hK σ hσ hp hp3 hex))
    (twistedE6_outer_commutator_odd hℓ hf hK σ hσ)
    (localCoreTrivialOn_noninner_twistedE6 hℓ hf hK σ hσ hp hp3)

theorem oddEndpoint_twistedE6_of_solvable_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p ℓ f : ℕ), p.Prime → 3 < p →
      ℓ.Prime → ℓ ≠ p → 1 ≤ f → Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
      Cond p ℓ f →
      (∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q) ∧
        (4 ≤ ℓ ^ f → ∀ x : twistedE6RootGroup K σ, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
            Group.IsSolvable V → IsCyclic V)) :
    OddEndpoint .twistedE6 Cond := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  have hm' : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (ℓ ^ f) := hmod.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm'
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  obtain ⟨hcyc, hcent⟩ := h K σ p ℓ f hp hp3 hℓ hℓp hf hK2 hσ hc
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_twistedE6_of_solvable_cyclic hℓ hf hK2 σ hσ hp hp3 hcyc hcent)).1

end CFSG.RankThree.PartOne.KE
