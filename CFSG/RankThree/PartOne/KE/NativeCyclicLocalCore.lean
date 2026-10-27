module

public import CFSG.RankThree.PartOne.KE.OddE6NoninnerCore
public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner
public import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LieType.Chevalley

theorem localCoreTrivialOn_noninner_E_even (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (adjointGroup τ K) =>
      α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  rcases hτ with rfl | hτ'
  · obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
    exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp hp3 B
        hB α hα hαp).2.2
  · have hNF := conj_normalForm_of_pointwise
      (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ').1
    exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp => by
      obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
      exact (even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ' hf K hK hp B hB
        α hα hαp x σ hxσ).2.2.2

theorem localCoreTrivialOn_noninner_E_odd (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (adjointGroup τ K) =>
      α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  rcases hτ with rfl | rfl | rfl
  · exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp hp3 B
        hB α hα hαp).2.2
  · exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp
        (by omega) B hB α hα hαp).2.2
  · exact localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2 hf K
        hK).2.2.2.2.2.2 hp B hB α hα hαp

theorem localCoreTrivialOn_noninner_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type)
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    LocalCoreTrivialOn p fun α : MulAut (adjointGroup τ K) =>
      α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  by_cases hℓ2 : ringChar K = 2
  · exact localCoreTrivialOn_noninner_E_even τ hτ n.pos K (by rw [hK, hℓ2]) hp hp3
  · exact localCoreTrivialOn_noninner_E_odd τ hτ hℓ hℓ2 n.pos K hK hp hp3

end CFSG.RankThree.PartOne.KE
