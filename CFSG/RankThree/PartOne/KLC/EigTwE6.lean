module

public import CFSG.RankThree.PartOne.KLC.TwE6Rank
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Lattice (wordMat toMat lget wordMat_eq_toMat)

open CFSG.RankThree.Chevalley (exhaustionPhi)


theorem perm_E6_vec (k : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm k = (![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k := by
  fin_cases k <;> rfl


theorem eigData_twE6_1 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q - 1) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6),
          (∑ l, U s l * Wm l ((![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k)) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat TwistTag.E6.tag [] = toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)
  refine ⟨(coxeterSystem TwistTag.E6.tag).wordProd [], toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![![1, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 0]], 0, 2,
    fun k l => smul_single_eq_lget' TwistTag.E6.tag _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget]

theorem eigData_twE6_2 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q + 1) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6),
          (∑ l, U s l * Wm l ((![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k)) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat TwistTag.E6.tag [] = toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)
  refine ⟨(coxeterSystem TwistTag.E6.tag).wordProd [], toMat 6 [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![![-1, 0, 0, 0, 0, 1], ![0, 0, -1, 0, 1, 0]], 0, 2,
    fun k l => smul_single_eq_lget' TwistTag.E6.tag _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 1) (B := 0) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-1, 0, 0, 0, 0, 1], ![0, 0, -1, 0, 1, 0]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_twE6_3 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + q + 1) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6),
          (∑ l, U s l * Wm l ((![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k)) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat TwistTag.E6.tag [4, 0, 2, 5, 5, 1, 5, 1, 5, 3, 0, 2, 1, 3, 4, 5, 2, 5, 1, 0, 5, 3, 1, 2, 3, 0] = toMat 6 [[0, 0, 1, -1, 1, -1], [0, 0, 0, -1, 2, -1], [-1, 0, 1, -1, 2, -2], [-1, 1, 1, -2, 3, -2], [0, 1, 0, -1, 2, -2], [0, 0, 0, 0, 1, -1]] :=
    wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)
  refine ⟨(coxeterSystem TwistTag.E6.tag).wordProd [4, 0, 2, 5, 5, 1, 5, 1, 5, 3, 0, 2, 1, 3, 4, 5, 2, 5, 1, 0, 5, 3, 1, 2, 3, 0], toMat 6 [[0, 0, 1, -1, 1, -1], [0, 0, 0, -1, 2, -1], [-1, 0, 1, -1, 2, -2], [-1, 1, 1, -2, 3, -2], [0, 1, 0, -1, 2, -2], [0, 0, 0, 0, 1, -1]], ![![(q + 2), 0, (-q), (2 * q), (-2 * q), -1], ![1, 2, (-2 * q - 1), (2 * q), 0, (-q - 1)]], 0, 2,
    fun k l => smul_single_eq_lget' TwistTag.E6.tag _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := 2 * q + 2) (B := 4 * q + 8) (N := 4) ?_
      (not_dvd_smooth hp hp5 (a := 2) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, -1, 2, -2, 0], ![0, 0, -2, 2, 0, -1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_twE6_4 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 + 1) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6),
          (∑ l, U s l * Wm l ((![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k)) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat TwistTag.E6.tag [1, 0, 0, 0, 3, 1, 5, 4, 1, 4, 4, 3, 1, 4, 2, 3, 2, 2, 4, 0, 2, 3, 2, 4, 1, 4, 5, 4, 3, 4, 1, 2, 3, 3] = toMat 6 [[1, 0, -1, 1, -1, 0], [1, -1, -1, 1, -1, 1], [2, 0, -2, 1, -1, 1], [3, -1, -2, 1, -1, 1], [2, -1, -2, 1, 0, 0], [1, 0, -1, 0, 0, 0]] :=
    wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)
  refine ⟨(coxeterSystem TwistTag.E6.tag).wordProd [1, 0, 0, 0, 3, 1, 5, 4, 1, 4, 4, 3, 1, 4, 2, 3, 2, 2, 4, 0, 2, 3, 2, 4, 1, 4, 5, 4, 3, 4, 1, 2, 3, 3], toMat 6 [[1, 0, -1, 1, -1, 0], [1, -1, -1, 1, -1, 1], [2, 0, -2, 1, -1, 1], [3, -1, -2, 1, -1, 1], [2, -1, -2, 1, 0, 0], [1, 0, -1, 0, 0, 0]], ![![(q), 0, (-q - 1), (q), (-q), (q + 1)], ![(q + 1), 1, -2, (q), (-2 * q - 1), (2 * q + 2)]], 0, 1,
    fun k l => smul_single_eq_lget' TwistTag.E6.tag _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := -q) (B := 1) (N := 1) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 0) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![1, 0, -1, 1, -1, 1], ![1, 0, 0, 1, -2, 2]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem eigData_twE6_6 {q : ℤ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hΦ : (p : ℤ) ∣ q^2 - q + 1) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (Wm : Matrix (Fin 6) (Fin 6) ℤ) (U : Fin 2 → Fin 6 → ℤ)
      (i j : Fin 6),
      (∀ k l : Fin 6, (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = Wm l k) ∧
      IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ) ∧
        ∀ (s : Fin 2) (k : Fin 6),
          (∑ l, U s l * Wm l ((![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) k)) ≡ q * U s k [ZMOD p] := by
  have hW : wordMat TwistTag.E6.tag [4, 3, 2, 0, 3] = toMat 6 [[-1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, 1, 1, -1, 1, 0], [-1, 1, 0, 0, 1, 0], [-1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]] :=
    wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)
  refine ⟨(coxeterSystem TwistTag.E6.tag).wordProd [4, 3, 2, 0, 3], toMat 6 [[-1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, 1, 1, -1, 1, 0], [-1, 1, 0, 0, 1, 0], [-1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]], ![![(-q), (q), 0, 0, -1, (-q + 2)], ![0, (2 * q - 1), (-q - 1), (-q + 2), (q - 2), (-q + 2)]], 0, 1,
    fun k l => smul_single_eq_lget' TwistTag.E6.tag _ _ hW k l, ?_, ?_⟩
  · refine isCoprime_of_cert hp hΦ (A := q + 1) (B := 2 * q + 3) (N := 3) ?_
      (not_dvd_smooth hp hp5 (a := 0) (b := 1) (by norm_num))
    simp
    ring
  · intro s k
    refine modEq_of_cert hΦ (c := ![![-1, 1, 0, 0, 0, -1], ![0, 2, -1, -1, 1, -1]] s k) ?_
    fin_cases s <;> fin_cases k <;> simp [Fin.sum_univ_succ, toMat, lget] <;> ring

theorem two_le_pRank_twistedE6_of_sector {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) {e : ℕ}
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) (h : (p : ℤ) ∣ (exhaustionPhi e).eval ((ℓ ^ f : ℕ) : ℤ)) :
    2 ≤ CFSG.pRank p (twistedE6RootGroup K σ) := by
  rcases he with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, Wm, U, i, j, hW, hd, hfx⟩ := eigData_twE6_1 (q := ((ℓ ^ f : ℕ) : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_twistedE6 hℓ hf K hK σ hσ hp hp5 hpℓ w Wm hW U i j hd fun s k => by
      rw [perm_E6_vec]
      exact hfx s k
  · obtain ⟨w, Wm, U, i, j, hW, hd, hfx⟩ := eigData_twE6_2 (q := ((ℓ ^ f : ℕ) : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_twistedE6 hℓ hf K hK σ hσ hp hp5 hpℓ w Wm hW U i j hd fun s k => by
      rw [perm_E6_vec]
      exact hfx s k
  · obtain ⟨w, Wm, U, i, j, hW, hd, hfx⟩ := eigData_twE6_3 (q := ((ℓ ^ f : ℕ) : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_twistedE6 hℓ hf K hK σ hσ hp hp5 hpℓ w Wm hW U i j hd fun s k => by
      rw [perm_E6_vec]
      exact hfx s k
  · obtain ⟨w, Wm, U, i, j, hW, hd, hfx⟩ := eigData_twE6_4 (q := ((ℓ ^ f : ℕ) : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_twistedE6 hℓ hf K hK σ hσ hp hp5 hpℓ w Wm hW U i j hd fun s k => by
      rw [perm_E6_vec]
      exact hfx s k
  · obtain ⟨w, Wm, U, i, j, hW, hd, hfx⟩ := eigData_twE6_6 (q := ((ℓ ^ f : ℕ) : ℤ)) hp hp5
      (by simpa [exhaustionPhi] using h)
    exact two_le_pRank_twistedE6 hℓ hf K hK σ hσ hp hp5 hpℓ w Wm hW U i j hd fun s k => by
      rw [perm_E6_vec]
      exact hfx s k

end CFSG.RankThree.PartOne.KLC
