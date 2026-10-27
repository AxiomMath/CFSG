module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.FlagSplit
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)

variable {K : Type} [Field K] [Finite K] {f : ℕ}

omit [Finite K] in
theorem unitaryFieldData_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem exists_flag_of_two_le_localRank_statedSU [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (hrk : 2 ≤ localRank p ↥(StatedSU n (2 ^ f) K)) :
    ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ n ∧ 2 ≤ a / d + (n - 2 * a) / d := by
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hrk
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have hexp : ∀ g ∈ E, g ^ p = 1 := fun g hg =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  obtain ⟨a, ha1, ha2, hcard⟩ := card_le_of_normalizes (unitaryForm 2 f hK n)
    (natRep (StatedSU n (2 ^ f) K)) (isIsometric_natRep_statedSU hK n) (natRep_injective _) hp hp2
    hpK hd hdiv hU2 hU0 hEU hcomm hexp
  rw [Module.finrank_fin_fun] at ha2 hcard
  rw [hEc, ← pow_add] at hcard
  exact ⟨a, ha1, ha2, (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard⟩

theorem not_dvd_pow_one_sub_one {p q : ℕ} (h : ¬ p ∣ q - 1) : ¬ p ∣ q ^ 1 - 1 := by
  simpa using h

theorem localRank_statedSU_four_le_one [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1) :
    localRank p ↥(StatedSU 4 (2 ^ f) K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSU hK hp hp2 (d := 2)
    (by norm_num)
    (fun i hi hid => by
      obtain rfl : i = 1 := by omega
      rw [hK]
      simpa using h1) hlt
  omega

theorem localRank_statedSU_five_le_one [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1) :
    localRank p ↥(StatedSU 5 (2 ^ f) K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSU hK hp hp2 (d := 2)
    (by norm_num)
    (fun i hi hid => by
      obtain rfl : i = 1 := by omega
      rw [hK]
      simpa using h1) hlt
  omega

theorem localRank_statedSU_six_le_one [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1) (h2 : ¬ p ∣ (2 ^ f) ^ 4 - 1) :
    localRank p ↥(StatedSU 6 (2 ^ f) K) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_flag_of_two_le_localRank_statedSU hK hp hp2 (d := 3)
    (by norm_num)
    (fun i hi hid => by
      rw [hK]
      obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
      · simpa using h1
      · rw [← pow_mul]
        exact h2) hlt
  omega

theorem localRank_statedProj_statedSU_le (hK : Nat.card K = (2 ^ f) ^ 2) {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ Nat.gcd n (2 ^ f + 1)) :
    localRank p (StatedProj (StatedSU n (2 ^ f) K)) ≤ localRank p ↥(StatedSU n (2 ^ f) K) := by
  have hcard := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn).2.2
  exact CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 _ (by rw [hcard]; exact hpn)

omit [Finite K] in
theorem card_statedSU_eq [CharP K 2] (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card (StatedSU n (2 ^ f) K) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) hn).2.1
  rw [show StatedSU n (2 ^ f) K = unitarySU 2 f K n from rfl, unitarySU_eq_gramSU h,
    card_gramSU, hU]

end CFSG.RankThree.PartOne.KFU
