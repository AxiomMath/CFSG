module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type} [Group G] [Finite G]

theorem mcBrideHypothesisB_two_of_coprime (H : Subgroup G) (h : Nat.Coprime 2 (Nat.card H)) :
    signalizerMcBrideHypothesisB 2 H := by
  refine ⟨Nat.prime_two, h, fun K L hKH _ _ _ hnc => ?_⟩
  exfalso
  have : Group.IsSolvable H := isSolvable_of_coprime_two H h
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKH)
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)

theorem two_signalizer_completion (A : Subgroup G) (hA : IsElemAbelian 2 A)
    (hrank : 8 ≤ Nat.card A) (θ : G → Subgroup G)
    (hcent : ∀ a ∈ A, a ≠ 1 → θ a ≤ Subgroup.centralizer {a})
    (hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (θ a)))
    (hinv : ∀ a ∈ A, a ≠ 1 → A ≤ Subgroup.normalizer (θ a : Set G))
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → θ a ⊓ Subgroup.centralizer {b} ≤ θ b) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Odd (Nat.card W) ∧ A ≤ Subgroup.normalizer (W : Set G) ∧
      (∀ a ∈ A, a ≠ 1 → W ⊓ Subgroup.centralizer {a} = θ a) ∧
      (∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
        (∀ a ∈ A, a ≠ 1 → Y ⊓ Subgroup.centralizer {a} ≤ θ a) → Y ≤ W) ∧
      Group.IsSolvable W := by
  intro W
  have hcop : ∀ a ∈ A, a ≠ 1 → Nat.Coprime 2 (Nat.card (θ a)) := fun a ha ha1 =>
    Nat.coprime_two_left.mpr (hodd a ha ha1)
  have hθ : IsSolvableSignalizerFunctor 2 A θ :=
    { le_centralizer := hcent
      coprime := hcop
      invariant := fun a ha ha1 x hx =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hinv a ha ha1 hx)
      balance := hbal
      solvable := fun a ha ha1 => isSolvable_of_coprime_two _ (hcop a ha ha1) }
  obtain ⟨hΘ, -⟩ := isSignalizerFunctor_elementValues Nat.prime_two hθ
  have hW : completion 2 1 A (elementValues θ) = W := completion_elementValues Nat.prime_two hA hθ
  obtain ⟨⟨hWcop, hWA⟩, hWcent, hWmax, hWsol⟩ :=
    signalizer_functor_theorem_two G 1 le_rfl A hA hrank (elementValues θ) hΘ.central
      hΘ.coprime hΘ.normalized hΘ.balanced
      (fun S hS => mcBrideHypothesisB_two_of_coprime _ (hΘ.coprime S hS))
  change Nat.Coprime 2 (Nat.card (completion 2 1 A (elementValues θ))) at hWcop
  change A ≤ Subgroup.normalizer (completion 2 1 A (elementValues θ) : Set G) at hWA
  change ∀ S ∈ signalizerFunctorEk 2 1 A,
    completion 2 1 A (elementValues θ) ⊓ Subgroup.centralizer (S : Set G) =
      elementValues θ S at hWcent
  change ∀ Y : Subgroup G, A ≤ Subgroup.normalizer (Y : Set G) →
    (∀ S ∈ signalizerFunctorEk 2 1 A, Y ⊓ Subgroup.centralizer (S : Set G) ≤ elementValues θ S) →
      Y ≤ completion 2 1 A (elementValues θ) at hWmax
  change (∀ S ∈ signalizerFunctorEk 2 1 A, Group.IsSolvable (elementValues θ S)) →
    Group.IsSolvable (completion 2 1 A (elementValues θ)) at hWsol
  rw [hW] at hWcop hWA hWcent hWmax hWsol
  refine ⟨Nat.coprime_two_left.mp hWcop, hWA, fun a ha ha1 => ?_, fun Y hY hYc => hWmax Y hY ?_,
    hWsol (isSignalizerFunctor_elementValues Nat.prime_two hθ).2⟩
  · have hz := zpowers_mem_E1 Nat.prime_two hA ha ha1
    rw [← centralizer_zpowers, hWcent _ hz,
      elementValues_eq Nat.prime_two hθ hz (Subgroup.mem_zpowers a) ha1]
  · intro S hS
    obtain ⟨a, haS, ha1⟩ := exists_ne_one_of_mem_E1 Nat.prime_two hS
    have hSa : Subgroup.zpowers a = S :=
      eq_zpowers_of_card_eq_prime Nat.prime_two (by rw [hS.2, pow_one]) haS ha1
    rw [elementValues_eq Nat.prime_two hθ hS haS ha1, ← hSa, centralizer_zpowers]
    exact hYc a (hS.1 haS) ha1

end CFSG.SignalizerFunctorTheorem
