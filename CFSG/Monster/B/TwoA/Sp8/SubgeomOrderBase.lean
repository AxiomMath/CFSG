
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGaussian

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

abbrev IsoSub (i : ℕ) : Type :=
  {W : Submodule (ZMod 2) V8 // IsTotallyIsotropic b0 W ∧ finrank (ZMod 2) W = i}

theorem natCard_inf_eq_subgroupOf (H K : Subgroup Dfull) :
    Nat.card ↥(K ⊓ H) = Nat.card (H.subgroupOf K) := by
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]

theorem factorization_two_pow_mul_of_not_dvd {n b : ℕ} (hb : ¬ 2 ∣ b) :
    (2 ^ n * b).factorization 2 = n := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero n two_ne_zero) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hb, add_zero]

theorem exists_sylow_le_of_card {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    {n a b : ℕ} (hH : Nat.card H = 2 ^ n * a) (hK : Nat.card K = 2 ^ n * b) (hb : ¬ 2 ∣ b) :
    ∃ P : Sylow 2 K, ∀ g ∈ (P : Subgroup K), (g : G) ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := n)
    (by rw [hH]; exact Dvd.intro a rfl)
  have hQ' : Nat.card (Q.map (Subgroup.inclusion hHK)) = 2 ^ (Nat.card K).factorization 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK), hQ, hK,
      factorization_two_pow_mul_of_not_dvd hb]
  refine ⟨Sylow.ofCard _ hQ', fun g hg => ?_⟩
  rw [Sylow.coe_ofCard] at hg
  obtain ⟨q, -, rfl⟩ := hg
  exact q.2

end CFSG.Monster.B.TwoA.Sp8
