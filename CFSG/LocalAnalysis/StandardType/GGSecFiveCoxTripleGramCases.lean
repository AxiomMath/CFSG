module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramDefs
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.StandardType.CoxTriple

private def ct_gc_admDec (N : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  (N 0 0 = 2 ∨ N 0 0 = 4) ∧ N 1 1 = N 0 0 ∧ (N 2 2 = 2 ∨ N 2 2 = 4) ∧ 2 * N 0 1 = -N 0 0 ∧
    N 0 0 ∣ 2 * N 0 1 ∧ N 0 0 ∣ 2 * N 0 2 ∧ N 1 1 ∣ 2 * N 1 2 ∧
    N 2 2 ∣ 2 * N 0 2 ∧ N 2 2 ∣ 2 * N 1 2 ∧
    ((2 * N 0 1 / N 0 0) * (2 * N 0 1 / N 1 1) = 0 ∨
      (2 * N 0 1 / N 0 0) * (2 * N 0 1 / N 1 1) = 1 ∨
      (2 * N 0 1 / N 0 0) * (2 * N 0 1 / N 1 1) = 2) ∧
    ((2 * N 0 2 / N 0 0) * (2 * N 0 2 / N 2 2) = 0 ∨
      (2 * N 0 2 / N 0 0) * (2 * N 0 2 / N 2 2) = 1 ∨
      (2 * N 0 2 / N 0 0) * (2 * N 0 2 / N 2 2) = 2) ∧
    ((2 * N 1 2 / N 1 1) * (2 * N 1 2 / N 2 2) = 0 ∨
      (2 * N 1 2 / N 1 1) * (2 * N 1 2 / N 2 2) = 1 ∨
      (2 * N 1 2 / N 1 1) * (2 * N 1 2 / N 2 2) = 2) ∧
    0 < N 0 0 * N 1 1 - N 0 1 ^ 2 ∧ 0 < N 0 0 * N 2 2 - N 0 2 ^ 2 ∧ 0 < N 1 1 * N 2 2 - N 1 2 ^ 2 ∧
    0 < N.det

private lemma ct_gc_admDec_of_admGram {N : Matrix (Fin 3) (Fin 3) ℤ} (h : AdmGram N) :
    ct_gc_admDec N := by
  obtain ⟨hsym, h00, h11, h22, h01, hdvd, hprod, hm01, hm02, hm12, hdet⟩ := h
  refine ⟨h00, h11, h22, h01, hdvd 0 1, hdvd 0 2, hdvd 1 2,
    by rw [← hsym 2 0]; exact hdvd 2 0, by rw [← hsym 2 1]; exact hdvd 2 1,
    hprod 0 1 (by decide), hprod 0 2 (by decide), hprod 1 2 (by decide),
    hm01, hm02, hm12, hdet⟩

theorem admGram_mem_admList {N : Matrix (Fin 3) (Fin 3) ℤ} (h : AdmGram N) : N ∈ admList := by
  have hAdm : AdmGram N := h
  obtain ⟨hsym, h00, h11, h22, h01, hdvd, hprod, hm01, hm02, hm12, hdet⟩ := h
  have h00lo : 2 ≤ N 0 0 := by rcases h00 with h | h <;> linarith
  have h00hi : N 0 0 ≤ 4 := by rcases h00 with h | h <;> linarith
  have h22lo : 2 ≤ N 2 2 := by rcases h22 with h | h <;> linarith
  have h22hi : N 2 2 ≤ 4 := by rcases h22 with h | h <;> linarith
  have h01lo : -2 ≤ N 0 1 := by rcases h00 with h | h <;> linarith [h01]
  have h01hi : N 0 1 ≤ -1 := by rcases h00 with h | h <;> linarith [h01]
  have hbound : N 0 0 * N 2 2 ≤ 16 := by
    rcases h00 with h | h <;> rcases h22 with h' | h' <;> nlinarith
  have h02sq : N 0 2 ^ 2 < 16 := by nlinarith [hm02, hbound]
  have h12sq : N 1 2 ^ 2 < 16 := by nlinarith [hm12, h11, hbound]
  have h02lo : -4 < N 0 2 := by nlinarith [h02sq, sq_nonneg (N 0 2 + 4)]
  have h02hi : N 0 2 < 4 := by nlinarith [h02sq, sq_nonneg (N 0 2 - 4)]
  have h12lo : -4 < N 1 2 := by nlinarith [h12sq, sq_nonneg (N 1 2 + 4)]
  have h12hi : N 1 2 < 4 := by nlinarith [h12sq, sq_nonneg (N 1 2 - 4)]
  have h01mem : N 0 1 ∈ Finset.Icc (-2 : ℤ) (-1) := by
    rw [Finset.mem_Icc]; exact ⟨h01lo, h01hi⟩
  have h02mem : N 0 2 ∈ Finset.Icc (-3 : ℤ) 3 := by
    rw [Finset.mem_Icc]; exact ⟨by linarith, by linarith⟩
  have h12mem : N 1 2 ∈ Finset.Icc (-3 : ℤ) 3 := by
    rw [Finset.mem_Icc]; exact ⟨by linarith, by linarith⟩
  have hN : N = !![N 0 0, N 0 1, N 0 2; N 0 1, N 0 0, N 1 2; N 0 2, N 1 2, N 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsym 1 0, hsym 2 0, hsym 2 1, h11]
  rw [hN] at hAdm ⊢
  have key : ∀ a ∈ ({2, 4} : Finset ℤ), ∀ b ∈ Finset.Icc (-2 : ℤ) (-1),
      ∀ f ∈ ({2, 4} : Finset ℤ), ∀ c ∈ Finset.Icc (-3 : ℤ) 3, ∀ e ∈ Finset.Icc (-3 : ℤ) 3,
      ct_gc_admDec !![a, b, c; b, a, e; c, e, f] → !![a, b, c; b, a, e; c, e, f] ∈ admList := by
    simp only [ct_gc_admDec]
    decide
  exact key (N 0 0) (by simpa using h00) (N 0 1) h01mem (N 2 2) (by simpa using h22)
    (N 0 2) h02mem (N 1 2) h12mem (ct_gc_admDec_of_admGram hAdm)

end CFSG.StandardType.CoxTriple

end
