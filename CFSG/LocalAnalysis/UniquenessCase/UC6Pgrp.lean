module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_of_isPGroup {p : ℕ} (hp : p.Prime) {S X : Subgroup G} (hS : IsPGroup p S)
    (hXS : X ≤ S) : IsSubnormal X S := by
  induction' hn : Nat.card S - Nat.card X using Nat.strong_induction_on with n ih generalizing X
  by_cases hXeq : X = S
  · subst hXeq
    exact IsSubnormal.refl _
  · have hlt : X < S := lt_of_le_of_ne hXS hXeq
    have hN : X < S ⊓ normalizer (X : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer p hp S X
        hS hlt
    have hXN : X ≤ S ⊓ normalizer (X : Set G) := hN.le
    have hXn : (X.subgroupOf (S ⊓ normalizer (X : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).2 inf_le_right
    have hcard : Nat.card X < Nat.card (S ⊓ normalizer (X : Set G) : Subgroup G) :=
      Subgroup.card_lt_of_lt hN
    have hle : Nat.card (S ⊓ normalizer (X : Set G) : Subgroup G) ≤ Nat.card S :=
      Subgroup.card_le_of_le inf_le_left
    exact IsSubnormal.step hXN hXn (ih _ (by omega) inf_le_left rfl)

theorem one_le_pRank_of_ne_bot {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) : 1 ≤ Open.pRank p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card X := hX.card_eq_or_dvd.resolve_left fun h =>
    hX1 (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxo : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  have hel : IsElemAbelian p (zpowers (x : G)) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  exact le_pRank_of_elemAbelian hp (zpowers_le.2 x.2) hel
    (by rw [Nat.card_zpowers, hxo, pow_one])

end CFSG.LocalAnalysis.UniquenessCase.UC6
