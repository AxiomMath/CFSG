module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA6

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

theorem pow_eight_of_two_pow_perm5 {y : Perm (Fin 5)} {k : ℕ} (h : y ^ 2 ^ k = 1) : y ^ 8 = 1 := by
  have h120 : y ^ 120 = 1 := by
    have := pow_card_eq_one' (G := Perm (Fin 5)) (x := y)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  have h2 : orderOf y ∣ 120 := orderOf_dvd_of_pow_eq_one h120
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj4
    have : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := this.trans h2
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow 2 hj3)

theorem sign_neg_of_comm_threeCyc :
    ∀ b : Perm (Fin 5), threeCyc012 * b = b * threeCyc012 → b ^ 8 = 1 → b ≠ 1 →
      Perm.sign b = -1 := by
  unfold threeCyc012
  decide +kernel

theorem sign_neg_of_comm {a b : Perm (Fin 5)} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hb8 : b ^ 8 = 1) (hb1 : b ≠ 1) : Perm.sign b = -1 := by
  obtain ⟨σ, hσ⟩ := exists_conj_threeCyc012 a ha3 ha1
  have h1 : threeCyc012 * (σ * b * σ⁻¹) = (σ * b * σ⁻¹) * threeCyc012 := by
    rw [← hσ]
    calc σ * a * σ⁻¹ * (σ * b * σ⁻¹) = σ * (a * b) * σ⁻¹ := by group
      _ = σ * (b * a) * σ⁻¹ := by rw [hab]
      _ = _ := by group
  have h2 : (σ * b * σ⁻¹) ^ 8 = 1 := by rw [conj_pow, hb8]; group
  have h3 : σ * b * σ⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have : b = σ⁻¹ * (σ * b * σ⁻¹) * σ := by group
    rw [this, h]; group
  have := sign_neg_of_comm_threeCyc _ h1 h2 h3
  have e : Perm.sign (σ * b * σ⁻¹) = Perm.sign b := by
    rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign σ), mul_assoc, mul_inv_cancel, mul_one]
  rwa [e] at this

end CFSG.Quasithin.F53
