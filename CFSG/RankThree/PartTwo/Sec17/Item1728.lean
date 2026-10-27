module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

section Scalar

variable {G : Type*} [Group G]

theorem pow_eq_pow_of_cast_eq {p : ℕ} {Z : Subgroup G}
    (hZe : CFSG.Assembly.IsElemAbelian p Z) {z : G} (hz : z ∈ Z) {a b : ℕ}
    (hab : (a : ZMod p) = (b : ZMod p)) : z ^ a = z ^ b := by
  rw [pow_eq_pow_iff_modEq]
  exact ((ZMod.natCast_eq_natCast_iff a b p).mp hab).of_dvd
    (orderOf_dvd_of_pow_eq_one (hZe.2 z hz))

theorem eq_bot_of_conj_eq_pow {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup G}
    (hZe : CFSG.Assembly.IsElemAbelian p Z) {c s : G}
    (hsZ : s ∈ Subgroup.normalizer (Z : Set G)) (hsc : s * c * s⁻¹ = c⁻¹) {m : ℕ}
    (hm : ((m : ZMod p)) ^ 2 ≠ 1) (hcm : ∀ z ∈ Z, c * z * c⁻¹ = z ^ m) : Z = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hs' : s⁻¹ ∈ Subgroup.normalizer (Z : Set G) := inv_mem hsZ
  have hsy : s⁻¹ * y * s ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp hs' y).mp hy
    simpa using this
  have hinv : c⁻¹ * y * c = y ^ m := by
    have hc' : c⁻¹ * y * c = s * (c * (s⁻¹ * y * s) * c⁻¹) * s⁻¹ := by
      have h1 : c⁻¹ * y * c = (s * c * s⁻¹) * y * (s * c * s⁻¹)⁻¹ := by rw [hsc, inv_inv]
      rw [h1]
      group
    rw [hc', hcm _ hsy]
    rw [show s * (s⁻¹ * y * s) ^ m * s⁻¹ = (s * (s⁻¹ * y * s) * s⁻¹) ^ m by
      rw [conj_pow]]
    group
  have hy2 : y ^ 1 = y ^ (m ^ 2) := by
    have h1 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    calc y ^ 1 = y := pow_one y
      _ = c * (c⁻¹ * y * c) * c⁻¹ := h1
      _ = c * y ^ m * c⁻¹ := by rw [hinv]
      _ = (c * y * c⁻¹) ^ m := by rw [conj_pow]
      _ = (y ^ m) ^ m := by rw [hcm y hy]
      _ = y ^ (m ^ 2) := by rw [← pow_mul, sq]
  rw [pow_eq_pow_iff_modEq] at hy2
  have hord : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hZe.2 y hy)
  rcases (Nat.dvd_prime hp.out).mp hord with h1 | hpord
  · rw [orderOf_eq_one_iff] at h1
    exact (Subgroup.mem_bot).mpr h1
  · exfalso
    rw [hpord] at hy2
    apply hm
    have := (ZMod.natCast_eq_natCast_iff 1 (m ^ 2) p).mpr hy2
    rw [Nat.cast_one, Nat.cast_pow] at this
    exact this.symm

end Scalar

end CFSG.RankThree.PartTwo.Sec17
