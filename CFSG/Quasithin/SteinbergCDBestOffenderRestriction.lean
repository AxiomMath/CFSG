module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG Subgroup CFSG.QuasithinUnique.Setup.Offender
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Groups

variable {G : Type*} [Group G]

theorem odd_card_center_of_pCore_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (h : CFSG.pCore 2 Q = ⊥) : Odd (Nat.card (center Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have hz' : orderOf (z : Q) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hn : (zpowers (z : Q)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g (z : Q) := mem_center_iff.mp z.2 g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k⟩
  have hp : IsPGroup 2 (zpowers (z : Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hle : zpowers (z : Q) ≤ CFSG.pCore 2 Q := le_sSup ⟨hn, hp⟩
  rw [h] at hle
  have h1 : (z : Q) = 1 := (mem_bot).mp (hle (mem_zpowers _))
  rw [h1, orderOf_one] at hz'
  norm_num at hz'

end Groups

end SteinbergCD

open Subgroup SteinbergCD CFSG.QuasithinUnique.Setup.Offender

end CFSG.Quasithin
