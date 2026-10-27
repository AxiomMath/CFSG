module

public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Lattice (wordMat toMat lget wordMat_eq_toMat)

open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups


theorem eigData_E6_1 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q - 1) :
    ∃ (w : WeylGroup Tag.E6) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E6 [2] = toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E6 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E6).wordProd [2], toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![![2, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0]], 0, 3,
    fun k l => smul_single_eq_lget' Tag.E6 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 2) ?_
      (not_dvd_smooth hp hp5 (a := 1) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![2, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget]
    ring

theorem eigData_E6_2 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q + 1) :
    ∃ (w : WeylGroup Tag.E6) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E6 [5, 3] = toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, -1, 1, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, -1]] :=
    wordMat_eq_toMat Tag.E6 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E6).wordProd [5, 3], toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, -1, 1, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, -1]], ![![0, 1, 1, -2, 1, 0], ![0, 0, 0, 0, 1, -2]], 1, 4,
    fun k l => smul_single_eq_lget' Tag.E6 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![0, 1, 1, -2, 1, 0], ![0, 0, 0, 0, 1, -2]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E6_3 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + q + 1) :
    ∃ (w : WeylGroup Tag.E6) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E6 [0, 5, 4, 2] = toMat 6 [[0, 0, -1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, -1, 1], [0, 0, 0, 1, -1, 0]] :=
    wordMat_eq_toMat Tag.E6 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E6).wordProd [0, 5, 4, 2], toMat 6 [[0, 0, -1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, -1, 1], [0, 0, 0, 1, -1, 0]], ![![(-q - 2), 0, (-q + 1), (q), 0, 0], ![0, 0, 0, (q + 1), (-2 * q - 1), (q - 1)]], 0, 3,
    fun k l => smul_single_eq_lget' Tag.E6 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 2 * q + 1) (B := 2 * q + 5) (N := 3) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 1) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-1, 0, -1, 1, 0, 0], ![0, 0, 0, 1, -2, 1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E6_4 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + 1) :
    ∃ (w : WeylGroup Tag.E6) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E6 [2, 4, 3, 1, 2, 3] = toMat 6 [[1, 0, 0, 0, 0, 0], [0, 0, 1, -1, 1, 0], [1, -1, 0, 0, 1, 0], [1, 0, 0, -1, 2, 0], [1, 0, 0, -1, 1, 1], [0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E6 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E6).wordProd [2, 4, 3, 1, 2, 3], toMat 6 [[1, 0, 0, 0, 0, 0], [0, 0, 1, -1, 1, 0], [1, -1, 0, 0, 1, 0], [1, 0, 0, -1, 2, 0], [1, 0, 0, -1, 1, 1], [0, 0, 0, 0, 0, 1]], ![![1, (-q - 1), (q - 1), (-q + 1), (q - 1), 1], ![(q + 1), (-q + 1), (-q - 1), 0, (q - 1), 1]], 0, 5,
    fun k l => smul_single_eq_lget' Tag.E6 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![0, -1, 1, -1, 1, 0], ![1, -1, -1, 0, 1, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E6_6 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 - q + 1) :
    ∃ (w : WeylGroup Tag.E6) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E6 [2, 3, 5, 4, 1, 2, 3, 2, 1, 0, 5, 4] = toMat 6 [[-1, 0, 1, 0, 0, 0], [-1, 0, 0, 1, -1, 1], [-2, 0, 1, 1, -1, 0], [-2, -1, 1, 2, -2, 1], [-1, -1, 0, 2, -1, 0], [-1, -1, 0, 1, 0, 0]] :=
    wordMat_eq_toMat Tag.E6 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E6).wordProd [2, 3, 5, 4, 1, 2, 3, 2, 1, 0, 5, 4], toMat 6 [[-1, 0, 1, 0, 0, 0], [-1, 0, 0, 1, -1, 1], [-2, 0, 1, 1, -1, 0], [-2, -1, 1, 2, -2, 1], [-1, -1, 0, 2, -1, 0], [-1, -1, 0, 1, 0, 0]], ![![(-q - 1), 0, (q), (q), (-q - 1), 1], ![(-2 * q), -2, 0, (2 * q), (-2 * q), (2 * q)]], 0, 2,
    fun k l => smul_single_eq_lget' Tag.E6 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -2 * q) (B := 4 * q + 4) (N := 4) ?_
      (not_dvd_smooth hp hp5 (a := 2) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-1, 0, 1, 1, -1, 0], ![-2, 0, 0, 2, -2, 2]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem two_le_pRank_E6_of_sector {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (h : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ)) :
    2 ≤ CFSG.pRank p (adjointGroup Tag.E6 K) := by
  rcases he with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E6_1 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 3 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E6_2 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 3 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E6_3 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 3 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E6_4 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 3 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E6_6 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 3 (by simp) hp (by omega) hpK w Wm hW U i j hd hf

end CFSG.RankThree.PartOne.KLC
