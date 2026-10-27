module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.GF2Rep417Diag

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem odd_card_center_of_pCore_eq_bot {L : Type} [Group L] [Finite L]
    (h : CFSG.pCore 2 L = ⊥) : Odd (Nat.card (Subgroup.center L)) := by
  by_contra hodd
  have hdvd : 2 ∣ Nat.card (Subgroup.center L) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hord : orderOf (z : L) = 2 := by
    simpa [hz] using orderOf_injective (Subgroup.center L).subtype Subtype.coe_injective z
  have hcard : Nat.card (Subgroup.zpowers (z : L)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers (z : L) ≤ CFSG.pCore 2 L :=
    le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2),
      IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)⟩
  rw [h] at hle
  have hz1 : (z : L) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  have hz1' : z = 1 := Subtype.ext hz1
  rw [hz1', orderOf_one] at hz
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.GF2Rep417Diag
