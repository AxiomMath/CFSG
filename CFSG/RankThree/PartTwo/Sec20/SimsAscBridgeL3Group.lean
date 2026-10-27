module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Walter.PSL2Facts.Even
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.Assembly.RankThreeEven (projSL)

theorem four_pow_mod_five (j : ℕ) : 4 ^ j % 5 = 1 ∨ 4 ^ j % 5 = 4 := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem two_pow_mod_five_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 5 = 2 ∨ 2 ^ m % 5 = 3 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod]
  rcases four_pow_mod_five j with h | h <;> norm_num [h]

theorem not_five_dvd_card_projSL3 {m : ℕ} (hm : Odd m) :
    ¬ 5 ∣ Nat.card (projSL 3 (GaloisField 2 m)) := by
  have hm0 : m ≠ 0 := by
    obtain ⟨j, rfl⟩ := hm
    omega
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 m)
  rw [GaloisField.card 2 m hm0] at h
  intro h5
  have h5' : 5 ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    h ▸ dvd_mul_of_dvd_left h5 _
  have hx := two_pow_mod_five_of_odd hm
  set x := 2 ^ m with hxdef
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hx2 : (x ^ 2) % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hx with h | h <;> rw [h]
  have hx3 : (x ^ 3) % 5 = 3 ∨ (x ^ 3) % 5 = 2 := by
    rw [Nat.pow_mod]
    rcases hx with h | h <;> rw [h] <;> norm_num
  have hy : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx1
  have hz : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx1
  have hp5 : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp5).mp h5' with h3 | h5''
  · omega
  · rcases (Nat.Prime.dvd_mul hp5).mp h5'' with h2 | h3
    · omega
    · omega

theorem five_dvd_card_projSL2 {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    5 ∣ Nat.card (projSL 2 (GaloisField 2 n)) := by
  rw [Nat.card_congr (Sec4.projSLEquivPSL (GaloisField 2 n)).toEquiv,
    CFSG.Walter.psl2_even_card hn0]
  obtain ⟨j, rfl⟩ := hn
  refine Dvd.dvd.mul_left ?_ _
  have h16 : (2 ^ (j + j)) ^ 2 = 16 ^ j := by
    rw [← pow_mul, show (j + j) * 2 = 4 * j by ring, pow_mul]
    norm_num
  rw [h16]
  have hmod : 16 ^ j % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ 16 ^ j := Nat.one_le_pow _ _ (by norm_num)
  omega

open scoped MatrixGroups in
theorem exists_orderOf_eq_four_SL3 (F : Type*) [Field F] [CharP F 2] :
    ∃ u : SL(3, F), orderOf u = 4 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let M : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 0, 1, 1; 0, 0, 1]
  have hdet : M.det = 1 := by simp [M, Matrix.det_fin_three]
  let u : SL(3, F) := ⟨M, hdet⟩
  have hu2 : ((u ^ 2 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, M, sq, Matrix.mul_apply, Fin.sum_univ_three, ← two_mul, h2]
  refine ⟨u, orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_⟩
  · intro h
    have h' := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
    simp only [pow_one] at h'
    rw [hu2] at h'
    simp at h'
  · refine Subtype.ext ?_
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow,
      hu2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_three, ← two_mul, h2]

theorem exists_orderOf_eq_four_projSL3 {n : ℕ} (hn : Odd n) :
    ∃ x : projSL 3 (GaloisField 2 n), orderOf x = 4 := by
  obtain ⟨u, hu⟩ := exists_orderOf_eq_four_SL3 (GaloisField 2 n)
  exact ⟨slThreeEquivProjSL hn u, by rw [MulEquiv.orderOf_eq, hu]⟩

end CFSG.RankThree.PartTwo.Sec20
