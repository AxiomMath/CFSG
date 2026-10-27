module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup

variable {G : Type*} [Group G]

@[expose] def semidihedralInvolution (y : Fin 8 × Fin 2) : Prop :=
  if (y.2 : ℕ) = 0 then (y.1 : ℕ) = 4 else (y.1 : ℕ) % 2 = 0

instance : DecidablePred semidihedralInvolution := fun y => by
  unfold semidihedralInvolution
  infer_instance

theorem semidihedral_quotient {Z : Subgroup G} [Z.Normal] (hZ : ∀ z ∈ Z, z ^ 3 = 1) {a b : G}
    (ha : orderOf a = 8) (hb : b ^ 2 = 1) (hrel : b * a * b = a ^ 3) :
    orderOf (a : G ⧸ Z) = 8 ∧ (b : G ⧸ Z) ^ 2 = 1 ∧
      (b : G ⧸ Z) * (a : G ⧸ Z) * (b : G ⧸ Z) = (a : G ⧸ Z) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, by rw [← QuotientGroup.mk_pow, hb, QuotientGroup.mk_one], by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hrel, QuotientGroup.mk_pow]⟩
  have h8 : (a : G ⧸ Z) ^ 2 ^ (2 + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, show 2 ^ (2 + 1) = orderOf a by rw [ha]; norm_num,
      pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h4 : ¬ (a : G ⧸ Z) ^ 2 ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    intro hmem
    have h3 := hZ _ hmem
    have h2 : (a ^ 2 ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 ^ 2 * 2 = orderOf a by rw [ha]; norm_num, pow_orderOf_eq_one]
    have h1 : a ^ 2 ^ 2 = 1 := by
      calc a ^ 2 ^ 2 = (a ^ 2 ^ 2) ^ 3 * ((a ^ 2 ^ 2) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, one_mul]
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  rw [orderOf_eq_prime_pow h4 h8]
  norm_num

end CFSG.Quasithin.SteinbergCD
