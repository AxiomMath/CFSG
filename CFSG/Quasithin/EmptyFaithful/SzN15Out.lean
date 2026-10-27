module

public import CFSG.Quasithin.EmptyFaithful.SzN15Good
public import CFSG.Quasithin.EmptyFaithful.SzN15Mat

public section

namespace CFSG.Quasithin.SzN15

open CFSG.QuasithinUnique

section Outcome

open CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

@[expose] def NatOutcome (X : Subgroup (MulAut V)) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), Nat.card K = 2 ^ m ∧
      (FFModel.nat (StatedSL 3 K)).Realizes X (commV X) (fixV X ⊓ commV X)) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), Nat.card K = 2 ^ m ∧
      (FFModel.nat (StatedSp 2 K)).Realizes X (commV X) (fixV X ⊓ commV X)) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ) (I : Fin 2 → Subgroup V)
      (π : ↥(StatedSL 3 K) →* ↥X), Nat.card K = 2 ^ m ∧ iSupIndep I ∧ (⨆ i, I i) = commV X ∧
      ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia X (I i) ⊥ π)

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])

theorem goodCoatom_of_natOutcome {X S : Subgroup (MulAut V)} (h : NatOutcome X)
    (hS : IsSylowTwoOf S X) : GoodCoatom X S := by
  have hUa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ commV X ↔ a u ∈ commV X :=
    fun a ha => commV_iff_apply ha
  have hZa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ fixV X ⊓ commV X ↔
      a u ∈ fixV X ⊓ commV X := fun a ha => inf_iff_apply (fixV_iff_apply ha) (commV_iff_apply ha)
  rcases h with ⟨K, _, _, m, hK, π, hπ⟩ | ⟨K, _, _, m, hK, π, hπ⟩ |
      ⟨K, _, _, m, I, π, hK, hind, hI, hreal⟩
  · have := charP_two_of_card hK
    exact (NatReal.of_realizesVia hπ).goodCoatom
      (fun T hT => sl3_Qt_covBy ⟨m, hK⟩ hT) hUa hZa hS
  · have := charP_two_of_card hK
    exact (NatReal.of_realizesVia hπ).goodCoatom
      (fun T hT => sp4_Qt_covBy ⟨m, hK⟩ hT) hUa hZa hS
  · have := charP_two_of_card hK
    have hsup : (⨆ i, I i) = I 0 ⊔ I 1 :=
      le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
        (sup_le (le_iSup I 0) (le_iSup I 1))
    exact goodCoatom_of_two (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
      (fun i => NatReal.of_realizesVia (hreal i))
      (fun T hT => sl3_Qt_covBy ⟨m, hK⟩ hT)
      (fun a ha u => by rw [← hsup, hI]; exact commV_iff_apply ha u) hS

end Outcome

end CFSG.Quasithin.SzN15
