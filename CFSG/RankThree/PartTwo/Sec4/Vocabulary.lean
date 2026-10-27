module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

@[expose] def IsSLThreePiAt (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K),
    (Nat.card K = q ∧ q % 3 = 1 ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ∨
      (Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 q K))

@[expose] def IsSLThreePi (X : Type) [Group X] : Prop :=
  ∃ q : ℕ, IsSLThreePiAt X q

@[expose] def IsSLThreeEpsAt (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K),
    (Nat.card K = q ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ∨
      (Nat.card K = q ^ 2 ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 q K))

@[expose] def IsTripleCover (X : Type*) [Group X] (Y : Type*) [Group Y] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ Nonempty (X ⧸ Subgroup.center X ≃* Y)

theorem IsTripleCover.isExtOf {X Y : Type*} [Group X] [Group Y] (h : IsTripleCover X Y) :
    IsExtOf X Y (Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, ⟨e⟩⟩ := h
  refine ⟨Subgroup.center X, inferInstance, ⟨mulEquivOfPrimeCardEq hcard ?_⟩, ⟨e⟩⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem isTripleCover_iff_isExtOf {X Y : Type*} [Group X] [Group Y] (hX : IsQuasisimple X)
    (hY : Subgroup.center Y = ⊥) :
    IsTripleCover X Y ↔ IsExtOf X Y (Multiplicative (ZMod 3)) := by
  refine ⟨IsTripleCover.isExtOf, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hKc : K ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hKn with h | h
    · exfalso
      have hX3 : Nat.card X = 3 := by
        rw [← Subgroup.card_top (G := X), ← h, hK3]
      have hcyc : IsCyclic X := isCyclic_of_prime_card hX3
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hcomm : ∀ x y : X, x * y = y * x := fun x y => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
        exact zpow_mul_comm g m n
      obtain ⟨a, b, hab⟩ := hX.2.2
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y => exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])
    · exact h
  have hcK : Subgroup.center X ≤ K := by
    have h1 : (Subgroup.center X).map (QuotientGroup.mk' K) ≤ Subgroup.center (X ⧸ K) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective K)
    have h2 : Subgroup.center (X ⧸ K) = ⊥ := by
      rw [← Subgroup.map_center_eq eQ.symm, hY, Subgroup.map_bot]
    rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have heq : Subgroup.center X = K := le_antisymm hcK hKc
  exact ⟨by rw [heq]; exact hK3, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans eQ⟩⟩

end CFSG.RankThree.PartTwo.Sec4
