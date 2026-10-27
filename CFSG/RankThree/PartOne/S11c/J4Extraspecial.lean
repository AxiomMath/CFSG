module

public import CFSG.RankThree.PartOne.S10.PlaneContract

public section

namespace CFSG.RankThree.PartOne

open CFSG Subgroup
open scoped commutatorElement

section Pairing

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

omit [Finite P] in
theorem card_center_le_of_noncomm (hcard : Nat.card P = p ^ 3)
    (hnc : ∃ a b : P, a * b ≠ b * a) : Nat.card (Subgroup.center P) ≤ p := by
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card (Subgroup.center P) ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hi2 : 2 ≤ i := by
    by_contra h
    have : i ≤ 1 := by omega
    have : p ^ i ≤ p := by
      calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos this
        _ = p := pow_one p
    omega
  have hidx : Nat.card (P ⧸ Subgroup.center P) = p ^ (3 - i) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    rw [hcard, hi'] at h
    have h2 : p ^ 3 = p ^ (3 - i) * p ^ i := by rw [← pow_add]; congr 1; omega
    have hpos : 0 < p ^ i := pow_pos hp.out.pos i
    rw [h2] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have hcyc : IsCyclic (P ⧸ Subgroup.center P) := by
    have hle : 3 - i ≤ 1 := by omega
    rcases Nat.lt_or_ge (3 - i) 1 with h0 | h1
    · have : 3 - i = 0 := by omega
      rw [this, pow_zero] at hidx
      have : Subsingleton (P ⧸ Subgroup.center P) := by
        have := Nat.card_eq_one_iff_unique.mp hidx
        exact this.1
      infer_instance
    · have : 3 - i = 1 := by omega
      rw [this, pow_one] at hidx
      have : Fact (Nat.card (P ⧸ Subgroup.center P)).Prime := ⟨hidx ▸ hp.out⟩
      exact isCyclic_of_prime_card hidx
  obtain ⟨a, b, hab⟩ := hnc
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center P)) (by rw [QuotientGroup.ker_mk'])
  exact hab (hcomm.is_comm.comm a b)

end Pairing

end CFSG.RankThree.PartOne
