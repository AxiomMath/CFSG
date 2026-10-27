module

public import CFSG.LocalAnalysis.StandardType.GGTWPatE7
public import CFSG.LocalAnalysis.StandardType.GGTWPatE8
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nT1R_a3 (i j : Fin 3) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nT1R_b3 (i j : Fin 3) : ℕ :=
  if i = j then 1
  else if ((i.val = 2 ∧ j.val = 1) ∨ (j.val = 2 ∧ i.val = 1)) then 4
  else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nT1R_a2 (i j : Fin 2) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private theorem l05nT1R_a3_apply (i j : Fin 3) :
    CoxeterMatrix.A 3 i j = l05nT1R_a3 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem l05nT1R_b3_apply (i j : Fin 3) :
    CoxeterMatrix.B 3 i j = l05nT1R_b3 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem l05nT1R_a2_apply (i j : Fin 2) :
    CoxeterMatrix.A 2 i j = l05nT1R_a2 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem l05nT1R_fin_A :
    ∀ e : Fin 3 ≃ Option (Fin 2),
      (∀ i j : Fin 2, l05nT1R_a3 (e.symm (some i)) (e.symm (some j)) = l05nT1R_a2 i j) →
      ∃ k : Fin 2, (k.val = 0 ∨ k.val + 1 = 2) ∧
        ∀ i, l05nT1R_a3 (e.symm none) (e.symm (some i)) = if i = k then 3 else 2 := by
  decide

private theorem l05nT1R_fin_B :
    ∀ e : Fin 3 ≃ Option (Fin 2),
      (∀ i j : Fin 2, l05nT1R_b3 (e.symm (some i)) (e.symm (some j)) = l05nT1R_a2 i j) →
      ∃ k : Fin 2, (k.val = 0 ∨ k.val + 1 = 2) ∧
        ∀ i, l05nT1R_b3 (e.symm none) (e.symm (some i)) = if i = k then 4 else 2 := by
  decide

private theorem l05nT1R_ext_L2_A (e : Fin 3 ≃ Option (Fin 2))
    (hJ : ∀ i j : Fin 2, (CoxeterMatrix.A 3).reindex e (some i) (some j) = CoxeterMatrix.A 2 i j) :
    ∃ k : Fin 2, (k.val = 0 ∨ k.val + 1 = 2) ∧
      ∀ i, (CoxeterMatrix.A 3).reindex e none (some i) = if i = k then 3 else 2 := by
  have h : ∀ i j : Fin 2,
      l05nT1R_a3 (e.symm (some i)) (e.symm (some j)) = l05nT1R_a2 i j := by
    intro i j
    have h1 := hJ i j
    rw [CoxeterMatrix.reindex_apply] at h1
    calc l05nT1R_a3 (e.symm (some i)) (e.symm (some j))
        = CoxeterMatrix.A 3 (e.symm (some i)) (e.symm (some j)) := (l05nT1R_a3_apply _ _).symm
      _ = CoxeterMatrix.A 2 i j := h1
      _ = l05nT1R_a2 i j := l05nT1R_a2_apply i j
  obtain ⟨k, hk, hrow⟩ := l05nT1R_fin_A e h
  refine ⟨k, hk, fun i => ?_⟩
  calc (CoxeterMatrix.A 3).reindex e none (some i)
      = CoxeterMatrix.A 3 (e.symm none) (e.symm (some i)) := by rw [CoxeterMatrix.reindex_apply]
    _ = l05nT1R_a3 (e.symm none) (e.symm (some i)) := l05nT1R_a3_apply _ _
    _ = if i = k then 3 else 2 := hrow i

private theorem l05nT1R_ext_L2_B (e : Fin 3 ≃ Option (Fin 2))
    (hJ : ∀ i j : Fin 2, (CoxeterMatrix.B 3).reindex e (some i) (some j) = CoxeterMatrix.A 2 i j) :
    ∃ k : Fin 2, (k.val = 0 ∨ k.val + 1 = 2) ∧
      ∀ i, (CoxeterMatrix.B 3).reindex e none (some i) = if i = k then 4 else 2 := by
  have h : ∀ i j : Fin 2,
      l05nT1R_b3 (e.symm (some i)) (e.symm (some j)) = l05nT1R_a2 i j := by
    intro i j
    have h1 := hJ i j
    rw [CoxeterMatrix.reindex_apply] at h1
    calc l05nT1R_b3 (e.symm (some i)) (e.symm (some j))
        = CoxeterMatrix.B 3 (e.symm (some i)) (e.symm (some j)) := (l05nT1R_b3_apply _ _).symm
      _ = CoxeterMatrix.A 2 i j := h1
      _ = l05nT1R_a2 i j := l05nT1R_a2_apply i j
  obtain ⟨k, hk, hrow⟩ := l05nT1R_fin_B e h
  refine ⟨k, hk, fun i => ?_⟩
  calc (CoxeterMatrix.B 3).reindex e none (some i)
      = CoxeterMatrix.B 3 (e.symm none) (e.symm (some i)) := by rw [CoxeterMatrix.reindex_apply]
    _ = l05nT1R_b3 (e.symm none) (e.symm (some i)) := l05nT1R_b3_apply _ _
    _ = if i = k then 4 else 2 := hrow i

private theorem l05nT1R_ext_L2 (e : Fin 3 ≃ Option (Fin 2)) {M : CoxeterMatrix (Option (Fin 2))}
    (hM : M = (CoxeterMatrix.A 3).reindex e ∨ M = (CoxeterMatrix.B 3).reindex e)
    (hJ : ∀ i j : Fin 2, M (some i) (some j) = CoxeterMatrix.A 2 i j) :
    ∃ (k : Fin 2) (μ : ℕ), (μ = 3 ∨ μ = 4) ∧ (k.val = 0 ∨ k.val + 1 = 2) ∧
      ∀ i, M none (some i) = if i = k then μ else 2 := by
  rcases hM with hMA | hMB
  · have hJ' : ∀ i j : Fin 2,
        (CoxeterMatrix.A 3).reindex e (some i) (some j) = CoxeterMatrix.A 2 i j := by
      intro i j; rw [← hMA]; exact hJ i j
    obtain ⟨k, hk, hrow⟩ := l05nT1R_ext_L2_A e hJ'
    exact ⟨k, 3, Or.inl rfl, hk, by intro i; rw [hMA]; exact hrow i⟩
  · have hJ' : ∀ i j : Fin 2,
        (CoxeterMatrix.B 3).reindex e (some i) (some j) = CoxeterMatrix.A 2 i j := by
      intro i j; rw [← hMB]; exact hJ i j
    obtain ⟨k, hk, hrow⟩ := l05nT1R_ext_L2_B e hJ'
    exact ⟨k, 4, Or.inr rfl, hk, by intro i; rw [hMB]; exact hrow i⟩

private theorem l05nT1_ext_dispatch {L : ℕ} (hL : 2 ≤ L)
    (hr : L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 6 ∨ L = 7)
    {M : CoxeterMatrix (Option (Fin L))} (hW : GGIsWeylMatrix M)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ (k : Fin L) (μ : ℕ), (μ = 3 ∨ μ = 4) ∧ (∀ i, M none (some i) = if i = k then μ else 2) ∧
      ((k.val = 0 ∨ k.val + 1 = L) ∨
        (μ = 3 ∧ 3 ≤ L ∧ (k.val = 1 ∨ k.val + 2 = L)) ∨
        (μ = 3 ∧ (L = 6 ∨ L = 7) ∧ (k.val = 2 ∨ k.val + 3 = L))) := by
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, e, _hn, hcase⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩
  · have hn1 : n = L + 1 := by
      have hcard := Fintype.card_congr e
      simpa [Fintype.card_fin, Fintype.card_option] using hcard
    subst n
    rcases hcase with hMA | ⟨_hn2, hMB⟩ | ⟨_hn4, hMD⟩
    · by_cases hL2 : L = 2
      · subst L
        obtain ⟨k, μ, hμ, hk, hrow⟩ := l05nT1R_ext_L2 e (Or.inl hMA) hJ
        exact ⟨k, μ, hμ, hrow, Or.inl hk⟩
      · have hL3 : 3 ≤ L := by omega
        obtain ⟨k, hk, hμ⟩ := ggDepA_ext_A hL3 e hMA hJ
        exact ⟨k, 3, Or.inl rfl, hμ, Or.inl hk⟩
    · by_cases hL2 : L = 2
      · subst L
        obtain ⟨k, μ, hμ, hk, hrow⟩ := l05nT1R_ext_L2 e (Or.inr hMB) hJ
        exact ⟨k, μ, hμ, hrow, Or.inl hk⟩
      · have hL3 : 3 ≤ L := by omega
        obtain ⟨k, hk, hμ⟩ := ggDepA_ext_B hL3 e hMB hJ
        exact ⟨k, 4, Or.inr rfl, hμ, Or.inl hk⟩
    · have hL3 : 3 ≤ L := by omega
      obtain ⟨k, hk, hμ⟩ := ggDepA_ext_D hL3 e hMD hJ
      exact ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inl ⟨rfl, hL3, hk⟩)⟩
  · exfalso
    have hcard := Fintype.card_congr e
    have h6 : (6 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    rcases hr with h | h | h | h | h <;> omega
  · have hcard := Fintype.card_congr e
    have h7 : (7 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    have hL6 : L = 6 := by omega
    subst L
    obtain ⟨k, hk, hμ⟩ := ggTW_ext_E7 e hMe hJ
    refine ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inr ⟨rfl, Or.inl rfl, ?_⟩)⟩
    rcases hk with h | h <;> omega
  · have hcard := Fintype.card_congr e
    have h8 : (8 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    have hL7 : L = 7 := by omega
    subst L
    obtain ⟨k, hk24, hμ⟩ := ggTW_ext_E8 e hMe hJ
    refine ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inr ⟨rfl, Or.inr rfl, ?_⟩)⟩
    rcases hk24 with h | h <;> omega
  · exfalso
    have hcard := Fintype.card_congr e
    have h4 : (4 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    have hL3 : L = 3 := by omega
    subst L
    exact (ggDepA_ext_F4 e hMe hJ).elim
  · exfalso
    have hcard := Fintype.card_congr e
    have h2 : (2 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega

theorem ggTW_pattern_abs {L : ℕ} (hL : 2 ≤ L)
    (hr : L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 6 ∨ L = 7)
    {M : CoxeterMatrix (Option (Fin L))} {C : Matrix (Option (Fin L)) (Option (Fin L)) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin L, C (some i) (some j) = CartanMatrix.A L i j) :
    ∃ (k : Fin L) (m n : ℤ),
      (((k.val = 0 ∨ k.val + 1 = L) ∧
          ((m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1))) ∨
        (3 ≤ L ∧ (k.val = 1 ∨ k.val + 2 = L) ∧ m = -1 ∧ n = -1) ∨
        (5 ≤ L ∧ L ≤ 7 ∧ (k.val = 2 ∨ k.val + 3 = L) ∧ m = -1 ∧ n = -1)) ∧
      ∀ i, C none (some i) = (if i = k then m else 0) ∧
        C (some i) none = (if i = k then n else 0) := by
  have hMA := l05nDP4_MJ hC hJ
  obtain ⟨k, μ, hμ, hrow, hpos⟩ := l05nT1_ext_dispatch hL hr hW hMA
  rcases hμ with rfl | rfl
  ·
    refine ⟨k, -1, -1, ?_, ?_⟩
    · rcases hpos with hend | ⟨-, hL3, hsec⟩ | ⟨-, hL67, hthird⟩
      · exact Or.inl ⟨hend, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr (Or.inl ⟨hL3, hsec, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega, hthird, rfl, rfl⟩)
    · intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 3 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, -⟩ | ⟨hm, h1, h2⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
  ·
    have hkM : M none (some k) = 4 := by rw [hrow k, if_pos rfl]
    have hprod : C none (some k) * C (some k) none = 2 ∧ C none (some k) < 0 ∧
        C (some k) none < 0 := by
      rcases hC.2 none (some k) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ |
        ⟨hm, -, -, -⟩
      · rw [hkM] at hm; omega
      · rw [hkM] at hm; omega
      · exact ⟨h1, h2, h3⟩
      · rw [hkM] at hm; omega
    have hend : k.val = 0 ∨ k.val + 1 = L := by
      rcases hpos with h | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · exact h
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) hprod.2.1 hprod.2.2 hprod.1 with
      ⟨hm1, hn2⟩ | ⟨hm2, hn1⟩
    · refine ⟨k, -1, -2, Or.inl ⟨hend, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm1 hn2; exact ⟨hm1, hn2⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
    · refine ⟨k, -2, -1, Or.inl ⟨hend, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm2 hn1; exact ⟨hm2, hn1⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega

end CFSG.StandardType

end
