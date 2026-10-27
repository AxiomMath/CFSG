module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nT8_a (n : ℕ) (i j : Fin n) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nT8_e8 (i j : Fin 8) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
          (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
          (i.val = 6 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6)
  then 3 else 2

private theorem l05nT8_e8_apply :
    ∀ p : Fin 8 × Fin 8, CoxeterMatrix.E₈ p.1 p.2 = l05nT8_e8 p.1 p.2 := by
  decide

private theorem l05nT8_a7_apply :
    ∀ p : Fin 7 × Fin 7, CoxeterMatrix.A 7 p.1 p.2 = l05nT8_a 7 p.1 p.2 := by
  decide

private def l05nT8_E8_hyp (a0 a1 a2 a3 a4 a5 a6 : Fin 8) : Prop :=
  l05nT8_e8 a0 a1 = 3 ∧ l05nT8_e8 a1 a2 = 3 ∧ l05nT8_e8 a2 a3 = 3 ∧
  l05nT8_e8 a3 a4 = 3 ∧ l05nT8_e8 a4 a5 = 3 ∧ l05nT8_e8 a5 a6 = 3 ∧
  a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a0 ≠ a4 ∧ a0 ≠ a5 ∧ a0 ≠ a6 ∧
  a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧ a1 ≠ a5 ∧ a1 ≠ a6 ∧
  a2 ≠ a3 ∧ a2 ≠ a4 ∧ a2 ≠ a5 ∧ a2 ≠ a6 ∧
  a3 ≠ a4 ∧ a3 ≠ a5 ∧ a3 ≠ a6 ∧ a4 ≠ a5 ∧ a4 ≠ a6 ∧ a5 ≠ a6

private theorem l05nT8_E8_path (a0 a1 a2 a3 a4 a5 a6 : Fin 8)
    (hh : l05nT8_E8_hyp a0 a1 a2 a3 a4 a5 a6) :
    (a0 = 0 ∧ a1 = 2 ∧ a2 = 3 ∧ a3 = 4 ∧ a4 = 5 ∧ a5 = 6 ∧ a6 = 7) ∨
    (a0 = 7 ∧ a1 = 6 ∧ a2 = 5 ∧ a3 = 4 ∧ a4 = 3 ∧ a5 = 2 ∧ a6 = 0) := by
  obtain ⟨h01, h12, h23, h34, h45, h56,
    d01, d02, d03, d04, d05, d06, d12, d13, d14, d15, d16,
    d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := hh
  fin_cases a0
  all_goals fin_cases a1
  all_goals (first | exfalso; exact absurd h01 (by decide) | skip)
  all_goals fin_cases a2
  all_goals (first | exfalso; exact absurd h12 (by decide) | skip)
  all_goals fin_cases a3
  all_goals (first | exfalso; exact absurd h23 (by decide) | skip)
  all_goals fin_cases a4
  all_goals (first | exfalso; exact absurd h34 (by decide) | skip)
  all_goals fin_cases a5
  all_goals (first | exfalso; exact absurd h45 (by decide) | skip)
  all_goals fin_cases a6
  all_goals (first | exfalso; exact absurd h56 (by decide) | skip)
  all_goals simp_all

private theorem l05nT8_E8_missing (t : Fin 8)
    (h0 : t ≠ 0) (h2 : t ≠ 2) (h3 : t ≠ 3) (h4 : t ≠ 4)
    (h5 : t ≠ 5) (h6 : t ≠ 6) (h7 : t ≠ 7) : t = 1 := by
  fin_cases t <;> simp_all

theorem ggTW_ext_E8 (e : Fin 8 ≃ Option (Fin 7)) {M : CoxeterMatrix (Option (Fin 7))}
    (hM : M = CoxeterMatrix.E₈.reindex e)
    (hJ : ∀ i j : Fin 7, M (some i) (some j) = CoxeterMatrix.A 7 i j) :
    ∃ k : Fin 7, (k.val = 2 ∨ k.val = 4) ∧ ∀ i, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin 7 → Fin 8 := fun i => e.symm (some i)
  let t : Fin 8 := e.symm none
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h2 : (some i : Option (Fin 7)) = some j := e.symm.injective (by simpa [f] using hij)
    exact Option.some.inj h2
  have hJ' : ∀ i j : Fin 7, l05nT8_e8 (f i) (f j) = l05nT8_a 7 i j := by
    intro i j
    have h1 : CoxeterMatrix.E₈ (f i) (f j) = CoxeterMatrix.A 7 i j := by
      have h := hJ i j
      rw [hM, CoxeterMatrix.reindex_apply] at h
      simpa [f] using h
    calc l05nT8_e8 (f i) (f j) = CoxeterMatrix.E₈ (f i) (f j) :=
          (l05nT8_e8_apply (f i, f j)).symm
      _ = CoxeterMatrix.A 7 i j := h1
      _ = l05nT8_a 7 i j := l05nT8_a7_apply (i, j)
  have hf_ne : ∀ i j : Fin 7, i ≠ j → f i ≠ f j := fun i j hij h => hij (hf_inj h)
  have ht_off : ∀ i : Fin 7, t ≠ f i := by
    intro i h
    have h' : (none : Option (Fin 7)) = some i := e.symm.injective (by simpa [t, f] using h)
    simp at h'
  have hhyp : l05nT8_E8_hyp (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hJ' 0 1]; decide
    · rw [hJ' 1 2]; decide
    · rw [hJ' 2 3]; decide
    · rw [hJ' 3 4]; decide
    · rw [hJ' 4 5]; decide
    · rw [hJ' 5 6]; decide
    · exact ⟨hf_ne 0 1 (by decide), hf_ne 0 2 (by decide), hf_ne 0 3 (by decide),
        hf_ne 0 4 (by decide), hf_ne 0 5 (by decide), hf_ne 0 6 (by decide),
        hf_ne 1 2 (by decide), hf_ne 1 3 (by decide), hf_ne 1 4 (by decide),
        hf_ne 1 5 (by decide), hf_ne 1 6 (by decide), hf_ne 2 3 (by decide),
        hf_ne 2 4 (by decide), hf_ne 2 5 (by decide), hf_ne 2 6 (by decide),
        hf_ne 3 4 (by decide), hf_ne 3 5 (by decide), hf_ne 3 6 (by decide),
        hf_ne 4 5 (by decide), hf_ne 4 6 (by decide), hf_ne 5 6 (by decide)⟩
  have hMi : ∀ i : Fin 7, M none (some i) = l05nT8_e8 t (f i) := by
    intro i
    rw [hM, CoxeterMatrix.reindex_apply]
    simpa only [t, f] using l05nT8_e8_apply (t, f i)
  have hp := l05nT8_E8_path (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) hhyp
  rcases hp with hfwd | hrev
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hfwd
    have ht1 : t = 1 :=
      l05nT8_E8_missing t
        (by simpa [h0] using ht_off 0)
        (by simpa [h1] using ht_off 1)
        (by simpa [h2] using ht_off 2)
        (by simpa [h3] using ht_off 3)
        (by simpa [h4] using ht_off 4)
        (by simpa [h5] using ht_off 5)
        (by simpa [h6] using ht_off 6)
    refine ⟨2, by decide, fun i => ?_⟩
    rw [hMi i, ht1]
    fin_cases i <;> simp_all [l05nT8_e8]
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hrev
    have ht1 : t = 1 :=
      l05nT8_E8_missing t
        (by simpa [h6] using ht_off 6)
        (by simpa [h5] using ht_off 5)
        (by simpa [h4] using ht_off 4)
        (by simpa [h3] using ht_off 3)
        (by simpa [h2] using ht_off 2)
        (by simpa [h1] using ht_off 1)
        (by simpa [h0] using ht_off 0)
    refine ⟨4, by decide, fun i => ?_⟩
    rw [hMi i, ht1]
    fin_cases i <;> simp_all [l05nT8_e8]

end CFSG.StandardType
