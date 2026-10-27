module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma add_one_lt_two_pow_sub_two {m : ℕ} (hm : 5 ≤ m) : m + 1 < 2 ^ (m - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  have key : ∀ j : ℕ, j + 6 < 2 ^ (j + 3) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show (j + 1) + 3 = j + 3 + 1 by omega, pow_succ]
      have hpos : 0 < 2 ^ (j + 3) := Nat.two_pow_pos _
      omega
  rw [show j + 5 - 2 = j + 3 by omega]
  simpa using key j

private lemma coxeterA_factorial_alt {r m : ℕ} (hrm : r ≠ m - 1) :
    r + 1 < m ∨ ¬ Nat.card (CoxeterMatrix.A r).Group ∣ (m + 1).factorial ∨
      Nat.card (CoxeterMatrix.A r).Group = (m + 1).factorial := by
  rw [l05nK3a_card_coxeterA]
  by_cases hlt : r + 1 < m
  · exact Or.inl hlt
  · rcases lt_or_eq_of_le (by omega : m ≤ r) with hmr | heq
    · right; left
      intro hd
      have hle := Nat.le_of_dvd (Nat.factorial_pos (m + 1)) hd
      have hfac := Nat.factorial_lt_of_lt (by omega : 0 < m + 1)
        (by omega : m + 1 < r + 1)
      omega
    · right; right
      rw [heq]

theorem card_coxeterD_not_dvd_factorial {k m : ℕ} (hm : 5 ≤ m) (hk : m - 1 ≤ k) :
    ¬ Nat.card (ggCoxeterMatrixD k).Group ∣ (m + 1).factorial := by
  have hk4 : 4 ≤ k := by omega
  by_cases hkm1 : k = m - 1
  · subst k
    rw [OrthF3.card_coxeterD_eq (m - 1) hk4,
      show m - 1 - 1 = m - 2 by omega]
    intro hd
    have hfac1 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
    have hfac2 : m.factorial = m * (m - 1).factorial := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using Nat.factorial_succ (m - 1)
    rw [hfac1, hfac2, ← mul_assoc] at hd
    have hdvd : 2 ^ (m - 2) ∣ m * (m + 1) := by
      have h := (Nat.mul_dvd_mul_iff_right (Nat.factorial_pos (m - 1))).mp hd
      rwa [mul_comm] at h
    have hcop : Nat.Coprime m (m + 1) :=
      (Nat.coprime_self_add_right).2 (Nat.coprime_one_right m)
    have hpp : IsPrimePow (2 ^ (m - 2)) :=
      Nat.prime_two.isPrimePow.pow (by omega : m - 2 ≠ 0)
    rcases (hcop.isPrimePow_dvd_mul hpp).mp hdvd with hdm | hdm
    · have hle := Nat.le_of_dvd (by omega : 0 < m) hdm
      have hb := add_one_lt_two_pow_sub_two hm
      omega
    · have hle := Nat.le_of_dvd (by omega : 0 < m + 1) hdm
      have hb := add_one_lt_two_pow_sub_two hm
      omega
  · by_cases hkm : k = m
    · subst k
      rw [OrthF3.card_coxeterD_eq m hk4, Nat.factorial_succ]
      intro hd
      have h2 : 2 ^ (m - 1) ∣ m + 1 :=
        (Nat.mul_dvd_mul_iff_right (Nat.factorial_pos m)).mp hd
      have hle := Nat.le_of_dvd (by omega : 0 < m + 1) h2
      have h1 : m + 1 < 2 ^ (m - 1) := by
        have hb := add_one_lt_two_pow_sub_two hm
        have hpow : 2 ^ (m - 2) ≤ 2 ^ (m - 1) :=
          Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
        omega
      omega
    · by_cases hkm1' : k = m + 1
      · subst k
        rw [OrthF3.card_coxeterD_eq (m + 1) hk4, Nat.add_sub_cancel]
        intro hd
        have hd' : 2 ^ m * (m + 1).factorial ∣ 1 * (m + 1).factorial := by
          simpa using hd
        have h2 : 2 ^ m ∣ 1 :=
          (Nat.mul_dvd_mul_iff_right (Nat.factorial_pos (m + 1))).mp hd'
        have hle := Nat.le_of_dvd (by norm_num : 0 < 1) h2
        have hge : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
        norm_num at hge
        omega
      · have hkgt : m + 1 < k := by omega
        rw [OrthF3.card_coxeterD_eq k hk4]
        intro hd
        have hle := Nat.le_of_dvd (Nat.factorial_pos (m + 1)) hd
        have hfac := Nat.factorial_lt_of_lt (by omega : 0 < m + 1) hkgt
        have hle' : k.factorial ≤ 2 ^ (k - 1) * k.factorial :=
          Nat.le_mul_of_pos_left k.factorial (Nat.two_pow_pos (k - 1))
        omega

private lemma not_dvd_factorial_coxeterE7
    {m : ℕ} (hm : m ≤ 8) :
    ¬ Nat.card (CoxeterMatrix.E₇).Group ∣ (m + 1).factorial := by
  rw [card_coxeterE7_group]
  intro hd
  have hle := Nat.le_of_dvd (Nat.factorial_pos (m + 1)) hd
  have hfac : (m + 1).factorial ≤ Nat.factorial 9 := Nat.factorial_le (by omega)
  norm_num at hfac
  omega

private lemma not_dvd_factorial_coxeterE8
    {m : ℕ} (hm : m ≤ 9) :
    ¬ Nat.card (CoxeterMatrix.E₈).Group ∣ (m + 1).factorial := by
  rw [card_coxeterE8_group]
  intro hd
  have hle := Nat.le_of_dvd (Nat.factorial_pos (m + 1)) hd
  have hfac : (m + 1).factorial ≤ Nat.factorial 10 := Nat.factorial_le (by omega)
  norm_num at hfac
  omega

theorem PZ.label_cases
    {lab : LargeEvenLabel} (hn : lab.n = 1) {m : ℕ} (hm : 5 ≤ m)
    (h : ggRowP_ESU 3 lab ∨ ggRowP_EOmM 3 lab ∨ ggRowP_ETwE6 3 lab ∨ ggRowP_EOmP 3 lab ∨
      ggRowP_EE7 3 lab ∨ ggRowP_EE8 3 lab ∨ ggRowP_NF4 3 lab) :
    (lab.tag = .twA ∧ lab.rank = m - 1 ∧ lab.n = 1) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) ∨
      (∃ (r m' N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt 3 lab r m' N C M ∧
          (N + 1 < m ∨ ¬ Nat.card M.Group ∣ (m + 1).factorial ∨
            Nat.card M.Group = (m + 1).factorial)) ∨
      GGF4ThreeLabel 3 lab ∨ GGTwE6BadLabel 3 lab := by
  obtain ⟨t, r, n⟩ := lab
  simp only at hn
  subst hn
  dsimp only at *
  simp only [ggRowP_ESU, ggRowP_EOmM, ggRowP_ETwE6, ggRowP_EOmP, ggRowP_EE7, ggRowP_EE8,
    ggRowP_NF4] at h
  rcases h with h | h | h | h | h | h | h
  ·
    obtain ⟨h1, -⟩ := h
    rcases h1 with ⟨ht, hr⟩ | ⟨ht, hr3⟩
    ·
      by_cases hrm : r = m - 1
      · exact Or.inl ⟨ht, hrm, rfl⟩
      · by_cases hr5 : r = 5
        · exact Or.inr (Or.inl ⟨ht, hr5, rfl⟩)
        · by_cases hdvd3 : 3 ∣ r + 1
          · refine Or.inr (Or.inr (Or.inl ⟨_, _, r, _, _,
              GGTBTorRowAt.aDep (Or.inr ht) ?_ hdvd3 (by simp [ggTorM, ht])
                (by dsimp only; rintro ⟨-, rfl, -⟩; omega), ?_⟩))
            · dsimp only
              obtain ⟨q, hq⟩ := hdvd3
              omega
            · exact coxeterA_factorial_alt hrm
          · refine Or.inr (Or.inr (Or.inl ⟨_, _, r, _, _,
              GGTBTorRowAt.aInd (Or.inr ht) hdvd3 (by simp [ggTorM, ht]), ?_⟩))
            · exact coxeterA_factorial_alt hrm
    ·
      subst hr3
      refine Or.inr (Or.inr (Or.inl ⟨_, _, 3, _, _,
        GGTBTorRowAt.d (Or.inr ⟨ht, by norm_num, ⟨1, by norm_num⟩⟩), Or.inl ?_⟩))
      omega
  ·
    obtain ⟨ht, -, hodd, -⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨_, _, r, _, _,
      GGTBTorRowAt.d (Or.inr ⟨ht, by norm_num, hodd⟩), ?_⟩))
    by_cases hlt : r + 1 < m
    · exact Or.inl hlt
    · exact Or.inr (Or.inl (card_coxeterD_not_dvd_factorial hm (by dsimp only; omega)))
  ·
    obtain ⟨ht, -⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, rfl, by norm_num⟩)))
  ·
    obtain ⟨ht, -, hev, -⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨_, _, r, _, _,
      GGTBTorRowAt.d (Or.inl ⟨ht, Or.inr ⟨by norm_num, hev⟩⟩), ?_⟩))
    by_cases hlt : r + 1 < m
    · exact Or.inl hlt
    · exact Or.inr (Or.inl (card_coxeterD_not_dvd_factorial hm (by dsimp only; omega)))
  ·
    obtain ⟨ht, -⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨_, _, 7, _, _,
      GGTBTorRowAt.e7 ht (by norm_num), ?_⟩))
    by_cases hlt : 8 < m
    · exact Or.inl hlt
    · exact Or.inr (Or.inl (not_dvd_factorial_coxeterE7 (by omega)))
  ·
    obtain ⟨ht, -⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨_, _, 8, _, _,
      GGTBTorRowAt.e8Three ht rfl, ?_⟩))
    by_cases hlt : 9 < m
    · exact Or.inl hlt
    · exact Or.inr (Or.inl (not_dvd_factorial_coxeterE8 (by omega)))
  ·
    obtain ⟨ht, -⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, rfl, by norm_num⟩)))

end CFSG.StandardType

end
