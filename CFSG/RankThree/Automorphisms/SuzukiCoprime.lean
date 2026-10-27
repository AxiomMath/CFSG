module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Blueprint
open CFSG.LieType.Suzuki (Suzuki_model_and_perfect_cover_outer_cyclicity)

theorem Suzuki_coprime_odd_prime_automorphism_subgroups_cyclic (T : Type) [Group T] (ℓ f : ℕ)
    (hT : SuzukiModel T ℓ f) {p : ℕ} (hp : p.Prime) (_hodd : Odd p) (hpT : ¬ p ∣ Nat.card T) :
    (∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut T, p ≤ Nat.card α.ker := by
  have : Finite T := by
    obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := hT
    exact Finite.of_equiv _ e.symm.toEquiv
  have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    (Suzuki_model_and_perfect_cover_outer_cyclicity.{0} T ℓ f hT).1.1
  have hcyc : ∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P := fun P hP =>
    isCyclic_of_isPGroup_of_outer hp hpT (fun Q _ => inferInstance) hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
