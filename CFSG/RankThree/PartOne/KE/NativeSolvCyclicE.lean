module

public import CFSG.RankThree.PartOne.KE.NativeSolvCyclic
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint
public import CFSG.RankThree.PartOne.KE.NativeCyclicLocalCore
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.LocalRank
open CFSG.RankThree.Chevalley CFSG.LieType.Chevalley

theorem p_dvd_exponent_of_noninner_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (α : MulAut (adjointGroup τ K))
    (hα : α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hαp : orderOf α = p) : p ∣ f := by
  have hαB : orderOf (⟨α, Subgroup.mem_top α⟩ : (⊤ : Subgroup (MulAut (adjointGroup τ K)))) =
      p := by rw [Subgroup.orderOf_mk, hαp]
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    rcases hτ with rfl | hτ'
    · obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
      exact (even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp
        hp3 ⊤ le_top ⟨α, Subgroup.mem_top α⟩ hα hαB).2.1
    · have hNF := conj_normalForm_of_pointwise
        (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ').1
      obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
      exact (even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ' hf K hK hp ⊤
        le_top ⟨α, Subgroup.mem_top α⟩ hα hαB x σ hxσ).2.1
  · rcases hτ with rfl | rfl | rfl
    · exact (odd_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp
        hp3 ⊤ le_top ⟨α, Subgroup.mem_top α⟩ hα hαB).1
    · exact (odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp
        (by omega) ⊤ le_top ⟨α, Subgroup.mem_top α⟩ hα hαB).1
    ·
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨-, -, -, hOut, -⟩ := odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2
        hf K hK
      have : Finite (adjointGroup .E8 K) := inferInstance
      have : Finite (MulAut (adjointGroup .E8 K)) := MulEquiv.finite_left
      have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (adjointGroup .E8 K)) :=
        inferInstance
      set π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup .E8 K)) with hπ
      have hπα : π α ≠ 1 := fun h =>
        hα ((QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner
          (adjointGroup .E8 K)) α).1 h)
      have hπp : (π α) ^ p = 1 := by rw [← map_pow, ← hαp, pow_orderOf_eq_one, map_one]
      have hord : orderOf (π α) = p :=
        orderOf_eq_prime hπp hπα
      have h1 : p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (adjointGroup .E8 K)) := hord ▸ orderOf_dvd_natCard (π α)
      rwa [hOut] at h1

theorem two_pow_le_card_of_noninner_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hex : ∃ α : MulAut (adjointGroup τ K),
      α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧ orderOf α = p) :
    2 ^ p ≤ Nat.card K := by
  obtain ⟨α, hα, hαp⟩ := hex
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hdvd := p_dvd_exponent_of_noninner_E τ hτ hℓ n.pos K hK hp hp3 α hα hαp
  have hpn : p ≤ (n : ℕ) := Nat.le_of_dvd n.pos hdvd
  calc 2 ^ p ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hpn
    _ ≤ ringChar K ^ (n : ℕ) := Nat.pow_le_pow_left hℓ.two_le _
    _ = Nat.card K := hK.symm

theorem planeLocalCoreOdd_of_solvable_cyclic_E (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hcyc : ∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q → IsCyclic Q)
    (hcent : 4 ≤ Nat.card K → ∀ x : adjointGroup τ K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup τ K))), V.Normal →
        Group.IsSolvable V → IsCyclic V) :
    PlaneLocalCoreOdd p (adjointGroup τ K) :=
  planeLocalCoreOdd_of_solvable_cyclic_abstract hp hp3 center_adjointGroup_eq_bot hcyc
    (fun hex => hcent (le_trans (by
      have : 4 ≤ 2 ^ p := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact this) (two_pow_le_card_of_noninner_E τ hτ K hp hp3 hex)))
    (ordinary_E_outer_derived_subgroup_odd τ hτ K).1 (localCoreTrivialOn_noninner_E τ hτ K hp hp3)

theorem oddEndpoint_E6_of_solvable_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E6 K), IsPGroup p Q → IsCyclic Q) ∧
        (4 ≤ Nat.card K → ∀ x : adjointGroup Tag.E6 K, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))), V.Normal →
            Group.IsSolvable V → IsCyclic V)) :
    OddEndpoint .E6 Cond := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_solvable_cyclic_E .E6 (Or.inl rfl) K hp hp3 hcyc hcent

theorem oddEndpoint_E7_of_solvable_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E7 K), IsPGroup p Q → IsCyclic Q) ∧
        (4 ≤ Nat.card K → ∀ x : adjointGroup Tag.E7 K, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))), V.Normal →
            Group.IsSolvable V → IsCyclic V)) :
    OddEndpoint .E7 Cond := by
  refine oddEndpoint_E7_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_solvable_cyclic_E .E7 (Or.inr (Or.inl rfl)) K hp hp3 hcyc hcent

theorem oddEndpoint_E8_of_solvable_cyclic {Cond : ℕ → ℕ → ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p ℓ f : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
      1 ≤ f → Nat.card K = ℓ ^ f → Cond p ℓ f →
      (∀ Q : Subgroup (adjointGroup Tag.E8 K), IsPGroup p Q → IsCyclic Q) ∧
        (4 ≤ Nat.card K → ∀ x : adjointGroup Tag.E8 K, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))), V.Normal →
            Group.IsSolvable V → IsCyclic V)) :
    OddEndpoint .E8 Cond := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨hcyc, hcent⟩ := h K p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_of_solvable_cyclic_E .E8 (Or.inr (Or.inr rfl)) K hp hp3 hcyc hcent

end CFSG.RankThree.PartOne.KE
