module

public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem R3E_J4_catalog_Schreier
    {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.J4)) :
    Group.IsSolvable (Outer T) := by
  obtain ⟨e⟩ := hT
  have : Finite NativeSporadic.J4 := fam_j4_simplicity.1
  have : Finite T := Finite.of_equiv _ e.toEquiv.symm
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  apply isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card (Outer T)).primeFactors ⊆ {2, 3} := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rcases (R3E_J4_outer_automorphism_group_no_large_primes ⟨e⟩).1 p hp.1 hp.2.1 with rfl | rfl
    · simp
    · simp
  exact (Finset.card_le_card hsub).trans (by decide)

theorem outer_J4_isSolvable :
    Group.IsSolvable (Outer NativeSporadic.J4) :=
  R3E_J4_catalog_Schreier ⟨MulEquiv.refl _⟩

end CFSG.Sporadic.J4Schreier
