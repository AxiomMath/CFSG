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


theorem eigData_F4_1 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q - 1) :
    ∃ (w : WeylGroup Tag.F4) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
      (i j : Fin 4),
      (∀ k l : Fin 4, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 4), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.F4 [] = toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.F4 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.F4).wordProd [], toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], ![![1, 0, 0, 0], ![0, 1, 0, 0]], 0, 1,
    fun k l => smul_single_eq_lget' Tag.F4 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0], ![0, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget]

theorem eigData_F4_2 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q + 1) :
    ∃ (w : WeylGroup Tag.F4) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
      (i j : Fin 4),
      (∀ k l : Fin 4, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 4), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.F4 [2, 0] = toMat 4 [[-1, 1, 0, 0], [0, 1, 0, 0], [0, 2, -1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat Tag.F4 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.F4).wordProd [2, 0], toMat 4 [[-1, 1, 0, 0], [0, 1, 0, 0], [0, 2, -1, 1], [0, 0, 0, 1]], ![![-2, 1, 0, 0], ![0, 2, -2, 1]], 1, 3,
    fun k l => smul_single_eq_lget' Tag.F4 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-2, 1, 0, 0], ![0, 2, -2, 1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_F4_3 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + q + 1) :
    ∃ (w : WeylGroup Tag.F4) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
      (i j : Fin 4),
      (∀ k l : Fin 4, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 4), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.F4 [0, 0, 3, 2, 3, 1, 2, 0, 3, 1, 2, 3, 3, 3, 1, 1, 1, 0, 1, 2, 1, 2, 2, 0] = toMat 4 [[-1, -1, 1, 0], [-1, -2, 1, 1], [-2, -2, 1, 1], [0, -2, 1, 0]] :=
    wordMat_eq_toMat Tag.F4 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.F4).wordProd [0, 0, 3, 2, 3, 1, 2, 0, 3, 1, 2, 3, 3, 3, 1, 1, 1, 0, 1, 2, 1, 2, 2, 0], toMat 4 [[-1, -1, 1, 0], [-1, -2, 1, 1], [-2, -2, 1, 1], [0, -2, 1, 0]], ![![(q), -1, 1, 0], ![-1, (q - 1), 1, 1]], 0, 2,
    fun k l => smul_single_eq_lget' Tag.F4 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0], ![0, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_F4_4 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + 1) :
    ∃ (w : WeylGroup Tag.F4) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
      (i j : Fin 4),
      (∀ k l : Fin 4, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 4), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.F4 [1, 2, 1, 2, 1, 3, 1, 3, 0, 2, 1, 3, 2, 0, 0, 1, 3, 2, 3, 0] = toMat 4 [[-1, 2, -1, 0], [-2, 3, -1, -1], [-2, 4, -1, -2], [-2, 2, 0, -1]] :=
    wordMat_eq_toMat Tag.F4 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.F4).wordProd [1, 2, 1, 2, 1, 3, 1, 3, 0, 2, 1, 3, 2, 0, 0, 1, 3, 2, 3, 0], toMat 4 [[-1, 2, -1, 0], [-2, 3, -1, -1], [-2, 4, -1, -2], [-2, 2, 0, -1]], ![![(q - 1), 2, -1, 0], ![-2, (q + 3), -1, -1]], 2, 3,
    fun k l => smul_single_eq_lget' Tag.F4 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0], ![0, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_F4_6 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 - q + 1) :
    ∃ (w : WeylGroup Tag.F4) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ)
      (i j : Fin 4),
      (∀ k l : Fin 4, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 4), (∑ l, U s l * Wm l k) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat Tag.F4 [3, 2, 1, 2, 0, 1, 0, 2] = toMat 4 [[0, 1, -1, 1], [-1, 1, -1, 2], [0, 0, -1, 3], [0, 0, -1, 2]] :=
    wordMat_eq_toMat Tag.F4 _ (by decide +kernel)
  refine ⟨(coxeterSystem Tag.F4).wordProd [3, 2, 1, 2, 0, 1, 0, 2], toMat 4 [[0, 1, -1, 1], [-1, 1, -1, 2], [0, 0, -1, 3], [0, 0, -1, 2]], ![![(q - 1), 1, -1, 1], ![-1, (q), -1, 2]], 0, 2,
    fun k l => smul_single_eq_lget' Tag.F4 _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := q - 1) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0], ![0, 1, 0, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem two_le_pRank_F4_of_sector {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (h : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ)) :
    2 ≤ CFSG.pRank p (adjointGroup Tag.F4 K) := by
  rcases he with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_F4_1 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_F4 hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_F4_2 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_F4 hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_F4_3 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_F4 hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_F4_4 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_F4 hp (by omega) hpK w Wm hW U i j hd hf
  · obtain ⟨w, Wm, U, i, j, hW, hd, hf⟩ := eigData_F4_6 (q := (Nat.card K : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_F4 hp (by omega) hpK w Wm hW U i j hd hf

end CFSG.RankThree.PartOne.KLC
