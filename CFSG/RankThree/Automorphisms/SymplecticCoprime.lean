module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (outer_isCyclic_of_isPGroup)

theorem symplectic_coprime_odd_prime_automorphism_subgroups_cyclic {K : Type} [Field K]
    [Finite K] {r : ℕ} (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (StatedProj (StatedSp r K))) :
    (∀ P : Subgroup (MulAut (StatedProj (StatedSp r K))), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (StatedProj (StatedSp r K)), p ≤ Nat.card α.ker := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hcyc : ∀ P : Subgroup (MulAut (StatedProj (StatedSp r K))), IsPGroup p P → IsCyclic P :=
    fun P hP => isCyclic_of_isPGroup_of_outer hp hpT
      (fun V hV => outer_isCyclic_of_isPGroup hℓ f.pos hK hr hp
        (hodd.ne_two_of_dvd_nat (dvd_refl p)) hV) hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
