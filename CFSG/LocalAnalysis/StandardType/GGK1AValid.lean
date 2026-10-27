module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1Av_ord_le_two (p n : ℕ) : ggMultOrd p n ≤ 2 := by
  unfold ggMultOrd
  split_ifs <;> omega

private theorem ggK1Av_ord_ne_zero {p n : ℕ} (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    ggMultOrd p n ≠ 0 := by
  rcases h with h | h
  · rw [ggMultOrd, if_pos h]; exact one_ne_zero
  · by_cases h1 : p ∣ 2 ^ n - 1
    · rw [ggMultOrd, if_pos h1]; exact one_ne_zero
    · rw [ggMultOrd, if_neg h1, if_pos h]; exact two_ne_zero

private theorem ggK1Av_two_pow_two_mul_sub_one (n : ℕ) :
    2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by ring, pow_mul]
  rw [h2, ← one_pow 2, Nat.sq_sub_sq]
  exact Nat.mul_comm _ _

private theorem ggK1Av_ord_two_mul_ne_zero {p n : ℕ}
    (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) : ggMultOrd p (2 * n) ≠ 0 := by
  apply ggK1Av_ord_ne_zero
  left
  rw [ggK1Av_two_pow_two_mul_sub_one]
  rcases h with h | h
  · exact h.mul_right _
  · exact h.mul_left _

private theorem ggK1Av_linear_adm {p nf N : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m)
    (hd0 : ggMultOrd p nf ≠ 0) :
    (false = false ∧ ggMultOrd p nf = 1) ∨ (false = true ∧ ggMultOrd p nf = 2) ∨
      (∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) := by
  rcases hm.blocks_eq with ⟨⟨_, _⟩, hsym, _⟩ | ⟨hnot, _, _⟩
  · exact Or.inr (Or.inr hsym)
  · by_cases h1 : ggMultOrd p nf = 1
    · exact Or.inl ⟨rfl, h1⟩
    · exfalso
      exact hnot ⟨by have := ggK1Av_ord_le_two p nf; omega, rfl⟩

private theorem ggK1Av_unitary_adm {p nf N : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m)
    (hd0 : ggMultOrd p nf ≠ 0) :
    (true = false ∧ ggMultOrd p nf = 1) ∨ (true = true ∧ ggMultOrd p nf = 2) ∨
      (∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) := by
  rcases hm.blocks_eq with ⟨⟨_, htw⟩, _, _⟩ | ⟨_, himp, _⟩
  · exact absurd htw (by decide)
  · by_cases h1 : ggMultOrd p nf = 1
    · exact Or.inr (Or.inr (himp ⟨h1, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, by have := ggK1Av_ord_le_two p nf; omega⟩)

theorem ggK1A_core_valid {p nf N d r : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hd : d = ggMultOrd p nf) (hr : N = r + 1) :
    GGMultValidCl ⟨.A, r, nf⟩ p (ggMultDatumA p nf d false m) := by
  have hd0 : ggMultOrd p nf ≠ 0 := ggK1Av_ord_ne_zero hdvd
  have hQ := ggK1Av_linear_adm hm hd0
  rw [hd]
  refine ⟨.A r, false, nf, by simp [ggKacTypeClOfLabel], ?_⟩
  exact (mem_ggMultTableCl_A hd0).mpr ⟨m, hm.length_eq, by rw [hm.sum_eq, hr], hQ, rfl⟩

theorem ggK1A_core_valid_D3 {p nf N d : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hd : d = ggMultOrd p nf) (hr : N = 4) :
    GGMultValidCl ⟨.D, 3, nf⟩ p (ggMultDatumA p nf d false m) := by
  have hd0 : ggMultOrd p nf ≠ 0 := ggK1Av_ord_ne_zero hdvd
  have hQ := ggK1Av_linear_adm hm hd0
  rw [hd]
  refine ⟨.A 3, false, nf, by simp [ggKacTypeClOfLabel], ?_⟩
  exact (mem_ggMultTableCl_A hd0).mpr ⟨m, hm.length_eq, by rw [hm.sum_eq, hr], hQ, rfl⟩

theorem ggK1A_core_valid_twD2 {p n N d : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} {m : List ℕ}
    (hm : GGK1AMultOf p (2 * n) N false K (xhat : GL (Fin N) K) m)
    (hdvd : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1)
    (hd : d = ggMultOrd p (2 * n)) (hr : N = 2) :
    GGMultValidCl ⟨.twD, 2, n⟩ p (ggMultDatumA p (2 * n) d false m) := by
  have hd0 : ggMultOrd p (2 * n) ≠ 0 := ggK1Av_ord_two_mul_ne_zero hdvd
  have hQ := ggK1Av_linear_adm hm hd0
  rw [hd]
  refine ⟨.A 1, false, 2 * n, by simp [ggKacTypeClOfLabel], ?_⟩
  exact (mem_ggMultTableCl_A hd0).mpr ⟨m, hm.length_eq, by rw [hm.sum_eq, hr], hQ, rfl⟩

theorem ggK1A_uni_core_valid {p nf N d r : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hd : d = ggMultOrd p nf) (hr : N = r + 1) :
    GGMultValidCl ⟨.twA, r, nf⟩ p (ggMultDatumA p nf d true m) := by
  have hd0 : ggMultOrd p nf ≠ 0 := ggK1Av_ord_ne_zero hdvd
  have hQ := ggK1Av_unitary_adm hm hd0
  rw [hd]
  refine ⟨.A r, true, nf, by simp [ggKacTypeClOfLabel], ?_⟩
  exact (mem_ggMultTableCl_A hd0).mpr ⟨m, hm.length_eq, by rw [hm.sum_eq, hr], hQ, rfl⟩

theorem ggK1A_uni_core_valid_twD3 {p nf N d : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hd : d = ggMultOrd p nf) (hr : N = 4) :
    GGMultValidCl ⟨.twD, 3, nf⟩ p (ggMultDatumA p nf d true m) := by
  have hd0 : ggMultOrd p nf ≠ 0 := ggK1Av_ord_ne_zero hdvd
  have hQ := ggK1Av_unitary_adm hm hd0
  rw [hd]
  refine ⟨.A 3, true, nf, by simp [ggKacTypeClOfLabel], ?_⟩
  exact (mem_ggMultTableCl_A hd0).mpr ⟨m, hm.length_eq, by rw [hm.sum_eq, hr], hQ, rfl⟩

end CFSG.StandardType

end
