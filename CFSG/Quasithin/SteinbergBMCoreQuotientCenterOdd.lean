module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

theorem five_core_quotient_center_odd {L : Type*} [Group L] [Finite L]
    (hQ : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    Group.IsPerfect (L ⧸ CFSG.pCore 2 L) ∧ CFSG.pCore 2 (L ⧸ CFSG.pCore 2 L) = ⊥ ∧
      Odd (Nat.card (center (L ⧸ CFSG.pCore 2 L))) := by
  have hO : CFSG.pCore 2 (L ⧸ CFSG.pCore 2 L) = ⊥ := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 L)
    have hker : IsPGroup 2 π.ker := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup
    have hle : (CFSG.pCore 2 (L ⧸ CFSG.pCore 2 L)).comap π ≤ CFSG.pCore 2 L :=
      le_sSup ⟨CFSG.pCore_normal.comap π, CFSG.pCore_isPGroup.comap_of_ker_isPGroup π hker⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 L) x
    exact (QuotientGroup.eq_one_iff y).mpr (hle hx)
  refine ⟨hQ.1, hO, ?_⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : zpowers (z : L ⧸ CFSG.pCore 2 L) ≤ center _ :=
    (zpowers_le (G := L ⧸ CFSG.pCore 2 L)).mpr z.2
  have hnorm : (zpowers (z : L ⧸ CFSG.pCore 2 L)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_center_iff.mp (hzc hn) g, mul_inv_cancel_right]
    exact hn
  have hp : IsPGroup 2 (zpowers (z : L ⧸ CFSG.pCore 2 L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
  have hle : zpowers (z : L ⧸ CFSG.pCore 2 L) ≤ CFSG.pCore 2 _ := le_sSup ⟨hnorm, hp⟩
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  have h1 : z = 1 := Subtype.ext hle
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

end CFSG.Quasithin.SteinbergBM
