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


theorem eigData_E8_1 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q - 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [6] = toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [6], toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]], ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1]], 0, 5,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 2) ?_
      (not_dvd_smooth hp hp5 (a := 1) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget]
    ring

theorem eigData_E8_2 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [4, 1] = toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [4, 1], toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![![0, -2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, -2, 1, 0, 0]], 3, 5,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![0, -2, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, -2, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_3 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + q + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [2, 6, 7, 0] = toMat 8 [[-1, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1, -1]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [2, 6, 7, 0], toMat 8 [[-1, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1, -1]], ![![(-2 * q - 1), 0, (q - 1), 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, (q + 1), (-q - 2), (-q + 1)]], 3, 5,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-2, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, -1, -1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_4 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [3, 1, 2, 3, 4, 2] = toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [1, 0, -1, 1, -1, 1, 0, 0], [1, 1, 0, 0, -1, 1, 0, 0], [1, 0, 0, 1, -2, 2, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [3, 1, 2, 3, 4, 2], toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [1, 0, -1, 1, -1, 1, 0, 0], [1, 1, 0, 0, -1, 1, 0, 0], [1, 0, 0, 1, -2, 2, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![![(q), (-q - 1), (-q + 1), (q - 1), (-q + 1), (q), 0, 0], ![(q + 1), (q - 1), (-q - 1), 0, (-q + 1), (q), 0, 0]], 0, 5,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, -1, -1, 1, -1, 1, 0, 0], ![1, 1, -1, 0, -1, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_5 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^4 + q^3 + q^2 + q + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2] = toMat 8 [[1, -1, -2, 2, -1, 1, -1, 1], [1, -2, -2, 3, -2, 2, -1, 0], [2, -2, -3, 4, -3, 2, -1, 1], [2, -3, -4, 6, -5, 4, -2, 1], [1, -2, -3, 5, -4, 3, -2, 1], [1, -2, -2, 4, -3, 2, -2, 1], [1, -1, -1, 2, -2, 2, -2, 1], [1, 0, -1, 1, -1, 1, -1, 0]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2], toMat 8 [[1, -1, -2, 2, -1, 1, -1, 1], [1, -2, -2, 3, -2, 2, -1, 0], [2, -2, -3, 4, -3, 2, -1, 1], [2, -3, -4, 6, -5, 4, -2, 1], [1, -2, -3, 5, -4, 3, -2, 1], [1, -2, -2, 4, -3, 2, -2, 1], [1, -1, -1, 2, -2, 2, -2, 1], [1, 0, -1, 1, -1, 1, -1, 0]], ![![(q^3 + 2 * q^2 + 2 * q + 1), (-q^2 - q - 1), (-2 * q^2 - 3 * q - 2), (2 * q^2 + 3 * q + 2), (-q^2 - 2 * q - 1), (q^2 + 2 * q + 1), (-q^2 - 2 * q - 1), (q^2 + q)], ![(q^2 + q + 1), (q^3 - q^2 - 2 * q - 1), (-2 * q^2 - 3 * q - 2), (3 * q^2 + 5 * q + 3), (-2 * q^2 - 4 * q - 3), (2 * q^2 + 3 * q + 2), (-q^2 - 2 * q - 1), (q)]], 0, 1,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 3 * q^3 + 3 * q^2 + 5) (B := -3 * q^5 - 3 * q^4 + 6 * q^3 + 10 * q^2 + 9 * q + 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_6 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 - q + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [5, 2, 4, 5, 7, 7, 3, 4, 1, 3, 5, 6] = toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, -1, 1, 0, 0, 0], [1, 0, 1, -1, 1, 0, -1, 1], [0, 0, 2, -1, 1, 0, -1, 1], [0, 0, 2, -1, 0, 1, -1, 1], [0, -1, 1, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [5, 2, 4, 5, 7, 7, 3, 4, 1, 3, 5, 6], toMat 8 [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, -1, 1, 0, 0, 0], [1, 0, 1, -1, 1, 0, -1, 1], [0, 0, 2, -1, 1, 0, -1, 1], [0, 0, 2, -1, 0, 1, -1, 1], [0, -1, 1, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]], ![![(q + 1), (-q), (q - 2), (-q + 2), -1, (q - 1), (-q + 1), (q)], ![(2 * q), 0, -2, (-q + 2), -1, 0, 1, (q - 1)]], 0, 4,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, -1, 1, -1, 0, 1, -1, 1], ![2, 0, 0, -1, 0, 0, 0, 1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_8 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^4 + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2] = toMat 8 [[-1, 0, 0, 1, 0, -1, 0, 1], [-1, -1, 0, 2, 0, -2, 1, 0], [-1, -1, -1, 3, 0, -2, 0, 1], [-1, -1, -1, 4, 0, -4, 1, 1], [0, -1, -1, 3, 0, -3, 1, 1], [0, 0, -1, 2, 0, -2, 1, 0], [0, 0, -1, 2, -1, -1, 1, 0], [0, 0, -1, 1, 0, -1, 1, 0]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2], toMat 8 [[-1, 0, 0, 1, 0, -1, 0, 1], [-1, -1, 0, 2, 0, -2, 1, 0], [-1, -1, -1, 3, 0, -2, 0, 1], [-1, -1, -1, 4, 0, -4, 1, 1], [0, -1, -1, 3, 0, -3, 1, 1], [0, 0, -1, 2, 0, -2, 1, 0], [0, 0, -1, 2, -1, -1, 1, 0], [0, 0, -1, 1, 0, -1, 1, 0]], ![![(q^3 - q^2), (-q), (-q), (q^2 + 2 * q + 1), -1, (-q^2 - 2 * q - 1), (q), (q^2 + 1)], ![(-q^2 - q - 1), (-q^2 - 2 * q - 1), (-q^2 - q - 1), (q^3 + 4 * q^2 + 5 * q + 3), (-q - 1), (-4 * q^2 - 5 * q - 3), (q^2 + q), (q^2 + 2 * q + 2)]], 0, 1,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := q + 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_10 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^4 - q^3 + q^2 - q + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2] = toMat 8 [[1, 0, -1, 1, -1, 1, -1, 1], [0, -1, -1, 2, -1, 1, -1, 1], [1, -1, -1, 2, -2, 2, -1, 1], [1, -2, -2, 4, -3, 3, -2, 1], [1, -1, -2, 3, -2, 2, -1, 0], [1, -1, -2, 3, -2, 1, 0, 0], [1, -1, -1, 2, -1, 0, 0, 0], [1, -1, -1, 1, 0, 0, 0, 0]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2, 3, 7, 1, 5, 4, 6, 0, 2], toMat 8 [[1, 0, -1, 1, -1, 1, -1, 1], [0, -1, -1, 2, -1, 1, -1, 1], [1, -1, -1, 2, -2, 2, -1, 1], [1, -2, -2, 4, -3, 3, -2, 1], [1, -1, -2, 3, -2, 2, -1, 0], [1, -1, -2, 3, -2, 1, 0, 0], [1, -1, -1, 2, -1, 0, 0, 0], [1, -1, -1, 1, 0, 0, 0, 0]], ![![(q^3 + q), (-q), (-q^2 - q - 1), (q^2 + q + 1), (-q^2 - 1), (q^2 + 1), (-q^2 - 1), (q^2)], ![(q), (q^3 - 2 * q^2 - 1), (-q^2 - q - 1), (2 * q^2 + q + 2), (-q^2 - q - 2), (q^2 + q + 1), (-q^2 - 1), (q^2 - q + 1)]], 0, 1,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q^3 + 2 * q^2 - q) (B := q^5 - 3 * q^4 + 2 * q^3 - q^2 + q + 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_E8_12 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^4 - q^2 + 1) :
    ∃ (w : WeylGroup Tag.E8) (Wm : Matrix (Fin 8) (Fin 8) ℤ) (U : Fin 2 → Fin 8 → ℤ)
      (i j : Fin 8),
      (∀ k l : Fin 8, (w • (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 8), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.E8 [3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2] = toMat 8 [[0, -1, 0, 1, 0, -1, 1, 0], [0, -1, -1, 2, 0, -1, 0, 1], [1, -1, -1, 2, 0, -2, 1, 1], [0, -1, -1, 3, 0, -3, 1, 2], [0, 0, -1, 2, 0, -2, 1, 1], [0, 0, 0, 1, 0, -1, 0, 1], [0, 0, 0, 1, 0, -1, 0, 0], [0, 0, 0, 1, -1, 0, 0, 0]] :=
    wordMat_eq_toMat Tag.E8 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.E8).wordProd [3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2, 3, 4, 2, 7, 1, 6, 0, 3, 4, 5, 3, 2], toMat 8 [[0, -1, 0, 1, 0, -1, 1, 0], [0, -1, -1, 2, 0, -1, 0, 1], [1, -1, -1, 2, 0, -2, 1, 1], [0, -1, -1, 3, 0, -3, 1, 2], [0, 0, -1, 2, 0, -2, 1, 1], [0, 0, 0, 1, 0, -1, 0, 1], [0, 0, 0, 1, 0, -1, 0, 0], [0, 0, 0, 1, -1, 0, 0, 0]], ![![(q^3 - q), (-q^2), -1, (q^2 + q + 1), 0, (-q^2 - 2 * q - 1), (q^2 + q), 0], ![(-q), (q^3 - q^2 - q), (-q^2), (2 * q^2 + 2 * q + 1), (-q - 1), (-q^2 - 2 * q - 1), (q), (q^2 + q)]], 0, 1,
    fun k l => smul_single_eq_lget' Tag.E8 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q^3 + q^2 + q - 1) (B := q^5 - 2 * q^4 - q^3 + 2 * q^2 + 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem two_le_pRank_E8_of_sector {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12)
    (h : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ)) :
    2 ≤ CFSG.pRank p (adjointGroup Tag.E8 K) := by
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_1 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_2 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_3 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_4 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_5 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_6 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_8 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_10 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_E8_12 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_E 1 (by simp) hp (by omega) hpK w Wm hW U i j hd hf

end CFSG.RankThree.PartOne.KLC
