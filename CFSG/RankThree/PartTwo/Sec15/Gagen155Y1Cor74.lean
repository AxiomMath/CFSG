module

public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

omit [Finite G] in
private lemma eq_one_of_sq_eq_one_of_pow_three_eq_one {x : G} (h2 : x ^ 2 = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have h6 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h7 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h8 : orderOf x = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h6 h7)
  exact orderOf_eq_one_iff.mp h8

omit [Finite G] in
private lemma conj_zpow_eq {s x : G} (h : s * x * s⁻¹ = x⁻¹) (j : ℤ) :
    s * x ^ j * s⁻¹ = x ^ (-j) := by
  have hconj : (MulAut.conj s) x = x⁻¹ := by
    rw [MulAut.conj_apply]
    exact h
  calc s * x ^ j * s⁻¹ = (MulAut.conj s) (x ^ j) := by rw [MulAut.conj_apply]
    _ = ((MulAut.conj s) x) ^ j := map_zpow _ _ j
    _ = (x⁻¹) ^ j := by rw [hconj]
    _ = x ^ (-j) := by rw [inv_zpow, zpow_neg]

omit [Finite G] in
private lemma exists_mul_zpow_of_mem_sup {A B : Subgroup G} [IsMulCommutative A] {u x : G}
    (hBA : B ≤ A) (huA : u ∈ A) (hx : x ∈ B ⊔ Subgroup.zpowers u) :
    ∃ b ∈ B, ∃ k : ℤ, b * u ^ k = x := by
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [Subgroup.mul_comm_of_mem_isMulCommutative A (Subgroup.zpow_mem A huA j) (hBA hy),
      mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hx' : x ∈ ((B ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers u) hnorm] at hx'
  obtain ⟨b, hb, t, ht, hbt⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  exact ⟨b, hb, k, hbt⟩

theorem mem_zpowers_of_conj_eq_inv {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : IsHyperplane A B) {a c s : G} (haA : a ∈ A) (haB : a ∉ B) (hcA : c ∈ A)
    (hcB : c ∉ B) (hsB : s ∈ Subgroup.centralizer (B : Set G)) (hsa : s * a * s⁻¹ = a⁻¹)
    (hsc : s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    c ∈ Subgroup.zpowers a := by
  haveI : IsMulCommutative A := hA.1
  have hBA' : B ≤ A := hBA.1
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h => hcB (by rw [h]; exact B.one_mem)
  have hsup : B ⊔ Subgroup.zpowers a = A :=
    Item148HJ.sup_zpowers_eq_of_isHyperplane hBA haA haB
  obtain ⟨b, hbB, k, hbt⟩ := exists_mul_zpow_of_mem_sup hBA' haA (hsup ▸ hcA)
  have hbA : b ∈ A := hBA' hbB
  have hsb : s * b * s⁻¹ = b := by
    have h := Subgroup.mem_centralizer_iff.mp hsB b hbB
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  have hscs : s * c * s⁻¹ = b * a ^ (-k) := by
    rw [← hbt, ← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply, hsb,
      conj_zpow_eq hsa k]
  have hmem : s * c * s⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hsc c).mp (Subgroup.mem_zpowers c)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hred : s * c * s⁻¹ = c ^ (m % 3) := by
    rw [← hm, zpow_eq_zpow_emod' m hc3]
    rfl
  have hbnd : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
    have h0 : (0 : ℤ) ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    have h1 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
    omega
  rcases hbnd with hm0 | hm1 | hm2
  ·
    have h1 : s * c * s⁻¹ = 1 := by rw [hred, hm0]; simp
    have h2 : c = 1 := by
      have h3 := congrArg (fun y => s⁻¹ * y * s) h1
      simpa [mul_assoc] using h3
    exact (hc1 h2).elim
  ·
    have h1 : b * a ^ (-k) = c := by rw [← hscs, hred, hm1]; simp
    have h2 : a ^ (-k) = a ^ k := mul_left_cancel (h1.trans hbt.symm)
    have h3 : (a ^ k) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h2]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h4 : (a ^ k) ^ 3 = 1 := by
      rw [show (a ^ k) ^ 3 = (a ^ k) ^ (((3 : ℕ) : ℤ)) by rw [zpow_natCast]]
      rw [← zpow_mul, show k * (((3 : ℕ) : ℤ)) = (((3 : ℕ) : ℤ)) * k by ring, zpow_mul,
        zpow_natCast, ha3, one_zpow]
    have h5 : a ^ k = 1 := eq_one_of_sq_eq_one_of_pow_three_eq_one h3 h4
    exact (hcB (by rw [← hbt, h5, mul_one]; exact hbB)).elim
  ·
    have hc2 : c ^ (2 : ℤ) = c⁻¹ := by
      have hxx : c * (c * c) = 1 := by
        simpa [pow_succ, mul_assoc] using hc3
      rw [zpow_two]
      exact eq_inv_of_mul_eq_one_right hxx
    have h1 : b * a ^ (-k) = c⁻¹ := by rw [← hscs, hred, hm2]; exact hc2
    have h2 : b * a ^ (-k) = b⁻¹ * a ^ (-k) := by
      calc b * a ^ (-k) = (b * a ^ k)⁻¹ := by rw [h1, hbt]
        _ = (a ^ k)⁻¹ * b⁻¹ := by rw [mul_inv_rev]
        _ = a ^ (-k) * b⁻¹ := by rw [zpow_neg]
        _ = b⁻¹ * a ^ (-k) := Subgroup.mul_comm_of_mem_isMulCommutative A
            (Subgroup.zpow_mem A haA (-k)) (hBA' (B.inv_mem hbB))
    have h3 : b = b⁻¹ := mul_right_cancel h2
    have h4 : b ^ 2 = 1 := by
      have h := congrArg (fun y => b * y) h3
      simpa [pow_two] using h
    have h5 : b = 1 := eq_one_of_sq_eq_one_of_pow_three_eq_one h4 (hA.2 b hbA)
    rw [← hbt, h5, one_mul]
    exact Subgroup.zpow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) k

theorem eq_of_conj_eq_inv {A B D : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : IsHyperplane A B) (hDA : IsHyperplane A D) {c s : G} (hcA : c ∈ A) (hcB : c ∉ B)
    (hcD : c ∉ D) (hsB : s ∈ Subgroup.centralizer (B : Set G)) (hsc : s * c * s⁻¹ = c⁻¹)
    (hsD : s ∈ Subgroup.normalizer (D : Set G)) : B = D := by
  haveI : IsMulCommutative A := hA.1
  have hBA' : B ≤ A := hBA.1
  have hDA' : D ≤ A := hDA.1
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h => hcB (by rw [h]; exact B.one_mem)
  have hsup : B ⊔ Subgroup.zpowers c = A :=
    Item148HJ.sup_zpowers_eq_of_isHyperplane hBA hcA hcB
  have hDB : D ≤ B := by
    intro x hxD
    have hxA : x ∈ A := hDA' hxD
    obtain ⟨b, hbB, j, hbt⟩ := exists_mul_zpow_of_mem_sup hBA' hcA (hsup ▸ hxA)
    have hbA : b ∈ A := hBA' hbB
    have hsb : s * b * s⁻¹ = b := by
      have h := Subgroup.mem_centralizer_iff.mp hsB b hbB
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have hsx : s * x * s⁻¹ = b * c ^ (-j) := by
      rw [← hbt, ← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply, hsb,
        conj_zpow_eq hsc j]
    have hsxD : s * x * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hsD x).mp hxD
    have hprodD : x * (s * x * s⁻¹)⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem hsxD)
    have hcomm : b * c ^ (2 * j) = c ^ (2 * j) * b :=
      Subgroup.mul_comm_of_mem_isMulCommutative A hbA (Subgroup.zpow_mem A hcA (2 * j))
    have heq : x * (s * x * s⁻¹)⁻¹ = c ^ (2 * j) := by
      rw [hsx, ← hbt, mul_inv_rev, show (c ^ (-j))⁻¹ = c ^ j by rw [zpow_neg, inv_inv]]
      have h1 : b * c ^ j * (c ^ j * b⁻¹) = b * (c ^ j * c ^ j) * b⁻¹ := by
        rw [mul_assoc b (c ^ j) (c ^ j * b⁻¹), mul_assoc b (c ^ j * c ^ j) b⁻¹,
          ← mul_assoc (c ^ j) (c ^ j) b⁻¹]
      rw [h1, ← zpow_add, show j + j = 2 * j by ring, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hc2jD : c ^ (2 * j) ∈ D := heq ▸ hprodD
    have hcjD : c ^ j ∈ D := by
      have hcj_eq : c ^ j = (c ^ (2 * j))⁻¹ := by
        have hc3' : c ^ (((3 : ℕ) : ℤ)) = 1 := by rw [zpow_natCast]; exact hc3
        have hc3j : c ^ (((3 : ℕ) : ℤ) * j) = 1 := by rw [zpow_mul, hc3', one_zpow]
        have hmul : c ^ j * c ^ (2 * j) = 1 := by
          rw [← zpow_add, show j + 2 * j = ((3 : ℕ) : ℤ) * j by ring, hc3j]
        exact eq_inv_of_mul_eq_one_left hmul
      rw [hcj_eq]
      exact D.inv_mem hc2jD
    by_cases hj : c ^ j = 1
    · rw [← hbt, hj, mul_one]
      exact hbB
    · exfalso
      have hcj3 : (c ^ j) ^ 3 = 1 := by
        rw [show (c ^ j) ^ 3 = (c ^ j) ^ (((3 : ℕ) : ℤ)) by rw [zpow_natCast]]
        rw [← zpow_mul, show j * (((3 : ℕ) : ℤ)) = (((3 : ℕ) : ℤ)) * j by ring, zpow_mul,
          zpow_natCast, hc3, one_zpow]
      have hordj : orderOf (c ^ j) = 3 := orderOf_eq_prime hcj3 hj
      have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
      have hzeq : Subgroup.zpowers (c ^ j) = Subgroup.zpowers c := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.zpow_mem (Subgroup.zpowers c) (Subgroup.mem_zpowers c) j
        · simp [Nat.card_zpowers, hordj, hordc]
      have hzD : Subgroup.zpowers (c ^ j) ≤ D := Subgroup.zpowers_le.mpr hcjD
      exact hcD (hzD (hzeq.symm ▸ Subgroup.mem_zpowers c))
  have hcard : Nat.card B = Nat.card D := by
    have h1 := hBA.2
    have h2 := hDA.2
    omega
  exact (Subgroup.eq_of_le_of_card_ge hDB (le_of_eq hcard)).symm

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
