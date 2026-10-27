module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem two_elt_mem_X (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {u : G} (huc : u ∈ Cen b) (huL : u ∈ CenS L) {k : ℕ} (hk : u ^ 2 ^ k = 1) :
    u ∈ Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, x, hx, hux⟩ := Q_decomp' h (Z_sq hA) u ⟨huc, huL⟩
  have hxc : x ∈ Cen b := FF79.L14.Opp_le 3 _ hx
  have hbx : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  have hcm : Commute (b ^ i) x := hbx.zpow_left i
  have hN : ¬ 3 ∣ 2 ^ k := fun hd => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hcN : (b ^ i) ^ (2 ^ k) * x ^ (2 ^ k) = 1 := by
    rw [← hcm.mul_pow, ← hux]; exact hk
  have hy : (b ^ i) ^ (2 ^ k) ∈ Opp 3 (Cen b) := by
    have : (b ^ i) ^ (2 ^ k) = (x ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hcN
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hx _)
  have hb3 : b ^ 3 = 1 := h.hyp.ord ▸ pow_orderOf_eq_one b
  have hbi3 : (b ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hy3 : ((b ^ i) ^ (2 ^ k)) ^ 3 = 1 := by rw [pow_right_comm, hbi3, one_pow]
  have hy1 : (b ^ i) ^ (2 ^ k) = 1 := by
    have d1 : orderOf ((b ^ i) ^ (2 ^ k)) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have d2 : orderOf ((b ^ i) ^ (2 ^ k)) ∣ Nat.card (Opp 3 (Cen b)) :=
      (Subgroup.orderOf_mk _ hy).symm ▸ Subgroup.orderOf_dvd_natCard _ hy
    have := Nat.eq_one_of_dvd_coprimes (FF79.L14.Opp_coprime 3 (Cen b)) d1 d2
    exact orderOf_eq_one_iff.mp this
  have hbi : b ^ i = 1 := by
    rw [← zpow_natCast, ← zpow_mul] at hy1
    have h1 : ((orderOf b : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr hy1
    rw [h.hyp.ord] at h1
    have h3 : (3 : ℤ) ∣ i := by
      rcases Int.prime_three.dvd_or_dvd h1 with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hN
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [h.hyp.ord]; exact h3)
  rw [hux, hbi, one_mul]; exact hx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
