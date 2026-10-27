module

public import CFSG.LieType.Universal.Unitary.Basic
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Unitary

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F) {n : ℕ}

theorem odd_natCard_of_le_center_SU {H : Subgroup (SU σ n)}
    (hH : H ≤ Subgroup.center (SU σ n)) : Odd (Nat.card H) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.mp heven)
  have hz2 : ((z : SU σ n) ^ 2) = 1 := by
    have hpow := pow_orderOf_eq_one z
    rw [hzord] at hpow
    simpa using congrArg (fun w : H => (w : SU σ n)) hpow
  have hz1 : (z : SU σ n) = 1 :=
    eq_one_of_mem_center_SU_of_sq_eq_one σ (hH z.2) hz2
  have hz : z = 1 := Subtype.ext hz1
  rw [hz] at hzord
  simp at hzord

theorem odd_orderOf_of_mem_center_SU {z : SU σ n}
    (hz : z ∈ Subgroup.center (SU σ n)) : Odd (orderOf z) := by
  have h := odd_natCard_of_le_center_SU σ (H := Subgroup.zpowers z) (Subgroup.zpowers_le.mpr hz)
  rwa [Nat.card_zpowers] at h

end CFSG.StandardType
