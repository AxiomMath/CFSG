module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

private lemma l05nK43s_pair_avoid (n : ℕ) (hn : 4 ≤ n) (b : Fin n) :
    ((⟨0, by omega⟩ : Fin n) ≠ b ∧ (⟨1, by omega⟩ : Fin n) ≠ b) ∨
      ((⟨2, by omega⟩ : Fin n) ≠ b ∧ (⟨3, by omega⟩ : Fin n) ≠ b) := by
  by_cases h0 : (⟨0, by omega⟩ : Fin n) = b
  · right
    have e2 : (⟨2, by omega⟩ : Fin n) ≠ b := by
      intro h
      have hv : (2 : ℕ) = 0 := by
        have := congrArg Fin.val (h.trans h0.symm)
        simpa using this
      omega
    have e3 : (⟨3, by omega⟩ : Fin n) ≠ b := by
      intro h
      have hv : (3 : ℕ) = 0 := by
        have := congrArg Fin.val (h.trans h0.symm)
        simpa using this
      omega
    exact ⟨e2, e3⟩
  · by_cases h1 : (⟨1, by omega⟩ : Fin n) = b
    · right
      have e2 : (⟨2, by omega⟩ : Fin n) ≠ b := by
        intro h
        have hv : (2 : ℕ) = 1 := by
          have := congrArg Fin.val (h.trans h1.symm)
          simpa using this
        omega
      have e3 : (⟨3, by omega⟩ : Fin n) ≠ b := by
        intro h
        have hv : (3 : ℕ) = 1 := by
          have := congrArg Fin.val (h.trans h1.symm)
          simpa using this
        omega
      exact ⟨e2, e3⟩
    · left
      exact ⟨h0, h1⟩

private lemma l05nK43s_fin_exists (n : ℕ) (hn : 4 ≤ n) (M : CoxeterMatrix (Fin n))
    (h01 : M (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 3)
    (h23 : M (⟨2, by omega⟩ : Fin n) (⟨3, by omega⟩ : Fin n) = 3) (b : Fin n) :
    ∃ i i' : Fin n, i ≠ b ∧ i' ≠ b ∧ i ≠ i' ∧ M i i' = 3 := by
  rcases l05nK43s_pair_avoid n hn b with ⟨h0, h1⟩ | ⟨h2, h3⟩
  · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, h0, h1, ?_, h01⟩
    intro h
    have hv : (0 : ℕ) = 1 := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, h2, h3, ?_, h23⟩
    intro h
    have hv : (2 : ℕ) = 3 := by
      have := congrArg Fin.val h
      simpa using this
    omega

private lemma l05nK43s_reindex_exists {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {e : Fin n ≃ Λ} {b : Λ}
    (h : ∃ i i' : Fin n, i ≠ e.symm b ∧ i' ≠ e.symm b ∧ i ≠ i' ∧ M i i' = 3) :
    ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧ j ≠ j' ∧ (M.reindex e).M j j' = 3 := by
  obtain ⟨i, i', hi, hi', hii, hM⟩ := h
  refine ⟨e i, e i', ?_, ?_, ?_, ?_⟩
  · intro hh
    exact hi (by simpa using congrArg e.symm hh)
  · intro hh
    exact hi' (by simpa using congrArg e.symm hh)
  · intro hh
    exact hii (e.injective hh)
  · rw [CoxeterMatrix.reindex_apply]
    simpa using hM

private lemma l05nK43s_gD_of (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (hD : CartanMatrix.D n i j = -1) : ggCoxeterMatrixD n i j = 3 := by
  rw [ggCoxeterMatrixD_apply, if_neg hij, if_neg (by rw [hD]; omega)]

private lemma l05nK43s_D01 (n : ℕ) (hn : 8 ≤ n) :
    ggCoxeterMatrixD n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 3 := by
  refine l05nK43s_gD_of n _ _ (by simp [Fin.ext_iff]) ?_
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk]
  rw [if_neg (by simp [Fin.ext_iff] : ¬ ((⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩))]
  rw [if_neg (by omega : ¬ n ≤ 2)]
  rw [if_pos (show True ∧ 1 + 2 < n from ⟨trivial, by omega⟩)]

private lemma l05nK43s_D23 (n : ℕ) (hn : 8 ≤ n) :
    ggCoxeterMatrixD n (⟨2, by omega⟩ : Fin n) (⟨3, by omega⟩ : Fin n) = 3 := by
  refine l05nK43s_gD_of n _ _ (by simp [Fin.ext_iff]) ?_
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.val_mk]
  rw [if_neg (by simp [Fin.ext_iff] : ¬ ((⟨2, by omega⟩ : Fin n) = ⟨3, by omega⟩))]
  rw [if_neg (by omega : ¬ n ≤ 2)]
  rw [if_pos (show True ∧ 3 + 2 < n from ⟨trivial, by omega⟩)]

private lemma l05nK43s_E8_key :
    ∀ b' : Fin 8, ∃ i i' : Fin 8, i ≠ b' ∧ i' ≠ b' ∧ i ≠ i' ∧ CoxeterMatrix.E₈.M i i' = 3 := by
  intro b'
  fin_cases b' <;>
    first
      | exact ⟨1, 3, by decide, by decide, by decide, by decide⟩
      | exact ⟨0, 2, by decide, by decide, by decide, by decide⟩

theorem ggRC_exists_simple_bond {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    (hW : GGIsWeylMatrix ML) (h8 : 8 ≤ Fintype.card Λ) (b : Λ) :
    ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧ j ≠ j' ∧ ML.M j j' = 3 := by
  rcases hW with ⟨n, e, _hn1, htype⟩ | ⟨e6, hE6⟩ | ⟨e7, hE7⟩ | ⟨e8, hE8⟩ | ⟨e4, hF4⟩ |
    ⟨e2, hG2⟩
  · have hc : Fintype.card Λ = n := by
      have h := Fintype.card_congr e.symm
      simpa using h
    have hn8 : 8 ≤ n := by omega
    rcases htype with hA | ⟨_hB2, hB⟩ | ⟨_hD4, hD⟩
    · rw [hA]
      exact l05nK43s_reindex_exists
        (l05nK43s_fin_exists n (by omega) (CoxeterMatrix.A n)
          (by simp [CoxeterMatrix.A, Matrix.of_apply])
          (by simp [CoxeterMatrix.A, Matrix.of_apply]) (e.symm b))
    · rw [hB]
      exact l05nK43s_reindex_exists
        (l05nK43s_fin_exists n (by omega) (CoxeterMatrix.B n)
          (by simp [CoxeterMatrix.B, Matrix.of_apply]; omega)
          (by simp [CoxeterMatrix.B, Matrix.of_apply]; omega) (e.symm b))
    · rw [hD]
      exact l05nK43s_reindex_exists
        (l05nK43s_fin_exists n (by omega) (ggCoxeterMatrixD n)
          (l05nK43s_D01 n hn8) (l05nK43s_D23 n hn8) (e.symm b))
  · exfalso
    have hc : Fintype.card Λ = 6 := by
      have h := Fintype.card_congr e6.symm
      simpa using h
    omega
  · exfalso
    have hc : Fintype.card Λ = 7 := by
      have h := Fintype.card_congr e7.symm
      simpa using h
    omega
  · rw [hE8]
    exact l05nK43s_reindex_exists (l05nK43s_E8_key (e8.symm b))
  · exfalso
    have hc : Fintype.card Λ = 4 := by
      have h := Fintype.card_congr e4.symm
      simpa using h
    omega
  · exfalso
    have hc : Fintype.card Λ = 2 := by
      have h := Fintype.card_congr e2.symm
      simpa using h
    omega

end CFSG.StandardType
