module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggF4H1Rows_rank_eq_three_of_card_coxeterA {n : ℕ}
    (h : Nat.card (CoxeterMatrix.A n).Group = 24) : n = 3 := by
  rw [l05nK3a_card_coxeterA] at h
  have h4 : Nat.factorial 4 = Nat.factorial (n + 1) := by rw [h]; norm_num
  have h41 : 4 = n + 1 := (Nat.factorial_inj (n := 4) (by norm_num)).mp h4
  omega

theorem ggF4H1Rows_card_coxeterB_ne (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (CoxeterMatrix.B n).Group ≠ 24 := by
  rcases n with _ | k
  · omega
  rcases k with _ | k
  · intro h
    have hBA : CoxeterMatrix.B 1 = CoxeterMatrix.A 1 := by
      apply CoxeterMatrix.ext
      ext i j
      fin_cases i
      fin_cases j
      decide
    rw [hBA, l05nK3a_card_coxeterA] at h
    norm_num at h
  · intro h
    rw [ggCoxeterB_card (k + 2) (by omega)] at h
    have hdvd : 2 ^ (k + 2) ∣ 24 := ⟨(k + 2).factorial, h.symm⟩
    have hle : 2 ^ (k + 2) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hk4 : k + 2 ≤ 4 := by
      by_contra hc
      have h5 : 5 ≤ k + 2 := by omega
      have h32 : 32 ≤ 2 ^ (k + 2) := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) h5
      omega
    have hk2 : k ≤ 2 := by omega
    interval_cases k <;> norm_num at h

theorem ggF4H1Rows_card_coxeterD_ne (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (ggCoxeterMatrixD n).Group ≠ 24 := by
  intro h
  rw [OrthF3.card_coxeterD_eq n hn] at h
  have h8 : 8 ≤ 2 ^ (n - 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h24 : Nat.factorial 4 ≤ Nat.factorial n := Nat.factorial_le (by omega)
  have hbig : 192 ≤ 2 ^ (n - 1) * n.factorial := by
    calc 192 = 8 * Nat.factorial 4 := by norm_num
      _ ≤ 2 ^ (n - 1) * n.factorial := Nat.mul_le_mul h8 h24
  omega

theorem ggF4H1_row_metadata
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt p lab r m N C M) (hM : Nat.card M.Group = 24) :
    (lab.tag = .A ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) := by
  cases hrow with
  | aDep htag h4 _ _ _ =>
      have h3 : lab.rank = 3 := ggF4H1Rows_rank_eq_three_of_card_coxeterA hM
      exact absurd h3 (by omega)
  | e6Three _ _ _ =>
      exact absurd hM (by rw [card_coxeterE6_group]; norm_num)
  | e8Three _ _ =>
      exact absurd hM (by rw [card_coxeterE8_group]; norm_num)
  | aInd htag _ hpm =>
      have h3 : lab.rank = 3 := ggF4H1Rows_rank_eq_three_of_card_coxeterA hM
      rcases htag with htag | htag
      · exact Or.inl ⟨htag, h3, by simpa [ggTorM, htag] using hpm⟩
      · exact Or.inr (Or.inl ⟨htag, h3, by simpa [ggTorM, htag] using hpm⟩)
  | c htag _ =>
      have h2 : 2 ≤ lab.rank := by
        rcases htag with htag | htag <;>
          · have h := hlab.2
            rw [htag] at h
            exact h.1
      exact absurd hM (ggF4H1Rows_card_coxeterB_ne lab.rank (by omega))
  | d hdisj =>
      have h3 : lab.rank = 3 := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -, hodd⟩
        · have hle : 3 ≤ lab.rank := by
            have h := hlab.2
            rw [hD] at h
            exact h
          by_contra hne
          exact ggF4H1Rows_card_coxeterD_ne lab.rank (by omega) hM
        · have hle : 2 ≤ lab.rank := by
            have h := hlab.2
            rw [htwD] at h
            exact h
          obtain ⟨k, hk⟩ := hodd
          by_contra hne
          exact ggF4H1Rows_card_coxeterD_ne lab.rank (by omega) hM
      rcases hdisj with ⟨hD, hpd⟩ | ⟨htwD, hpd, -⟩
      · refine Or.inr (Or.inr (Or.inl ⟨hD, h3, ?_⟩))
        rcases hpd with h | ⟨-, heven⟩
        · exact h
        · rw [h3] at heven
          obtain ⟨k, hk⟩ := heven
          omega
      · exact Or.inr (Or.inr (Or.inr ⟨htwD, h3, hpd⟩))
  | e6Ind _ _ _ =>
      exact absurd hM (by rw [card_coxeterE6_group]; norm_num)
  | e7 _ _ =>
      exact absurd hM (by rw [card_coxeterE7_group]; norm_num)
  | e8Ind _ _ _ =>
      exact absurd hM (by rw [card_coxeterE8_group]; norm_num)
  | f4 _ _ _ =>
      exact absurd hM (by rw [l04fFRC_ord_card_coxeterF4]; norm_num)
  | g2 _ _ =>
      exact absurd hM (by rw [l04fFRC_card_coxeterG2]; norm_num)
  | relD hdisj =>
      have hk : 1 ≤ lab.rank - 1 := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -⟩
        · have h := hlab.2
          rw [hD] at h
          omega
        · have h := hlab.2
          rw [htwD] at h
          omega
      exact absurd hM (ggF4H1Rows_card_coxeterB_ne (lab.rank - 1) hk)
  | relE6 _ _ =>
      exact absurd hM (by rw [l04fFRC_ord_card_coxeterF4]; norm_num)
  | relA5 _ _ =>
      exact absurd hM (ggF4H1Rows_card_coxeterB_ne 3 (by norm_num))

end CFSG.StandardType

end
