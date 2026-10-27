module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nT7_a (n : ℕ) (i j : Fin n) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nT7_e7 (i j : Fin 7) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
          (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)
  then 3 else 2

private theorem l05nT7_e7_apply :
    ∀ p : Fin 7 × Fin 7, CoxeterMatrix.E₇ p.1 p.2 = l05nT7_e7 p.1 p.2 := by
  decide

private theorem l05nT7_a6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.A 6 p.1 p.2 = l05nT7_a 6 p.1 p.2 := by
  decide

private def l05nT7_E7_hyp (a0 a1 a2 a3 a4 a5 : Fin 7) : Prop :=
  l05nT7_e7 a0 a1 = 3 ∧ l05nT7_e7 a1 a2 = 3 ∧ l05nT7_e7 a2 a3 = 3 ∧
  l05nT7_e7 a3 a4 = 3 ∧ l05nT7_e7 a4 a5 = 3 ∧
  a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a0 ≠ a4 ∧ a0 ≠ a5 ∧
  a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧ a1 ≠ a5 ∧
  a2 ≠ a3 ∧ a2 ≠ a4 ∧ a2 ≠ a5 ∧
  a3 ≠ a4 ∧ a3 ≠ a5 ∧ a4 ≠ a5

private theorem l05nT7_E7_path (a0 a1 a2 a3 a4 a5 : Fin 7)
    (hh : l05nT7_E7_hyp a0 a1 a2 a3 a4 a5) :
    (a0 = 0 ∧ a1 = 2 ∧ a2 = 3 ∧ a3 = 4 ∧ a4 = 5 ∧ a5 = 6) ∨
    (a0 = 6 ∧ a1 = 5 ∧ a2 = 4 ∧ a3 = 3 ∧ a4 = 2 ∧ a5 = 0) := by
  obtain ⟨h01, h12, h23, h34, h45,
    d01, d02, d03, d04, d05, d12, d13, d14, d15,
    d23, d24, d25, d34, d35, d45⟩ := hh
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
  all_goals simp_all

private theorem l05nT7_E7_missing (t : Fin 7)
    (h0 : t ≠ 0) (h2 : t ≠ 2) (h3 : t ≠ 3) (h4 : t ≠ 4)
    (h5 : t ≠ 5) (h6 : t ≠ 6) : t = 1 := by
  fin_cases t <;> simp_all

theorem ggTW_ext_E7 (e : Fin 7 ≃ Option (Fin 6)) {M : CoxeterMatrix (Option (Fin 6))}
    (hM : M = CoxeterMatrix.E₇.reindex e)
    (hJ : ∀ i j : Fin 6, M (some i) (some j) = CoxeterMatrix.A 6 i j) :
    ∃ k : Fin 6, (k.val = 2 ∨ k.val = 3) ∧ ∀ i, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin 6 → Fin 7 := fun i => e.symm (some i)
  let t : Fin 7 := e.symm none
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h2 : (some i : Option (Fin 6)) = some j := e.symm.injective (by simpa [f] using hij)
    exact Option.some.inj h2
  have hJ' : ∀ i j : Fin 6, l05nT7_e7 (f i) (f j) = l05nT7_a 6 i j := by
    intro i j
    have h1 : CoxeterMatrix.E₇ (f i) (f j) = CoxeterMatrix.A 6 i j := by
      have h := hJ i j
      rw [hM, CoxeterMatrix.reindex_apply] at h
      simpa [f] using h
    calc l05nT7_e7 (f i) (f j) = CoxeterMatrix.E₇ (f i) (f j) :=
          (l05nT7_e7_apply (f i, f j)).symm
      _ = CoxeterMatrix.A 6 i j := h1
      _ = l05nT7_a 6 i j := l05nT7_a6_apply (i, j)
  have hf_ne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j hij h => hij (hf_inj h)
  have ht_off : ∀ i : Fin 6, t ≠ f i := by
    intro i h
    have h' : (none : Option (Fin 6)) = some i := e.symm.injective (by simpa [t, f] using h)
    simp at h'
  have hhyp : l05nT7_E7_hyp (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hJ' 0 1]; decide
    · rw [hJ' 1 2]; decide
    · rw [hJ' 2 3]; decide
    · rw [hJ' 3 4]; decide
    · rw [hJ' 4 5]; decide
    · exact hf_ne 0 1 (by decide)
    · exact hf_ne 0 2 (by decide)
    · exact hf_ne 0 3 (by decide)
    · exact hf_ne 0 4 (by decide)
    · exact hf_ne 0 5 (by decide)
    · exact hf_ne 1 2 (by decide)
    · exact hf_ne 1 3 (by decide)
    · exact hf_ne 1 4 (by decide)
    · exact hf_ne 1 5 (by decide)
    · exact hf_ne 2 3 (by decide)
    · exact hf_ne 2 4 (by decide)
    · exact hf_ne 2 5 (by decide)
    · exact hf_ne 3 4 (by decide)
    · exact hf_ne 3 5 (by decide)
    · exact hf_ne 4 5 (by decide)
  have hMi : ∀ i : Fin 6, M none (some i) = l05nT7_e7 t (f i) := by
    intro i
    rw [hM, CoxeterMatrix.reindex_apply]
    simpa only [t, f] using l05nT7_e7_apply (t, f i)
  have hp := l05nT7_E7_path (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) hhyp
  rcases hp with hfwd | hrev
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfwd
    have ht1 : t = 1 :=
      l05nT7_E7_missing t
        (by simpa [h0] using ht_off 0)
        (by simpa [h1] using ht_off 1)
        (by simpa [h2] using ht_off 2)
        (by simpa [h3] using ht_off 3)
        (by simpa [h4] using ht_off 4)
        (by simpa [h5] using ht_off 5)
    refine ⟨2, by decide, fun i => ?_⟩
    rw [hMi i, ht1]
    fin_cases i <;> simp_all [l05nT7_e7]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hrev
    have ht1 : t = 1 :=
      l05nT7_E7_missing t
        (by simpa [h5] using ht_off 5)
        (by simpa [h4] using ht_off 4)
        (by simpa [h3] using ht_off 3)
        (by simpa [h2] using ht_off 2)
        (by simpa [h1] using ht_off 1)
        (by simpa [h0] using ht_off 0)
    refine ⟨3, by decide, fun i => ?_⟩
    rw [hMi i, ht1]
    fin_cases i <;> simp_all [l05nT7_e7]

end CFSG.StandardType

end
