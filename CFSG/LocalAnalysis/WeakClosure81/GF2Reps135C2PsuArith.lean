module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslArith
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem c2suar_labelStar_ne_of_natural {n : ℕ} (hn : 3 ≤ n) (j : Fin n)
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) : labelStar j ≠ j := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  intro h
  have h1 := congrArg Fin.val h
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  omega

private theorem c2suar_labelStar_ne_five {n : ℕ} (hn5 : n = 5) (j : Fin n)
    (hj : (j : ℕ) = 2 ∨ (j : ℕ) = 3) : labelStar j ≠ j := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  intro h
  have h1 := congrArg Fin.val h
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  omega

theorem w135c2_psu_classify_three {n f s : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    (hs : 1 ≤ s) (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (hact : ∃ r, ε r ≠ ∅) (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hns : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 →
      (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s)
    (hmv : s * movedTop (by omega : 2 ≤ n) ε ≤ 6) :
    (∃ (r₀ : Fin f) (j : Fin n), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) ∧ f = 1) ∨
      (n = 4 ∧ f = 1 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 2 ∧ ∀ r, ε r = {j}) := by
  classical
  have hn2 : 2 ≤ n := by omega
  rcases w135c2_psl_classify_three hn2 hs ε h0 hact hper hmv with
    ⟨r₀, j, hone, hεj, hj⟩ | h4 | ⟨hn5, hf1, hs1, j, hj, hεall⟩ | ⟨hn3, hf1, -, -⟩ |
    ⟨hn2', -, -, -⟩
  ·
    have hr₀ : ε r₀ ≠ ∅ := by
      rw [hεj]
      exact Finset.singleton_ne_empty j
    have hcard : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 := by
      have hsub : (univ.filter fun r => ε r ≠ ∅) ⊆ {r₀} := by
        intro r hr
        rw [Finset.mem_singleton]
        by_contra hne
        exact (Finset.mem_filter.mp hr).2 (hone r hne)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h1
      omega
    have hnsd : ∃ r, (ε r).image labelStar ≠ ε r := by
      refine ⟨r₀, ?_⟩
      rw [hεj, Finset.image_singleton]
      intro h
      exact c2suar_labelStar_ne_of_natural hn j hj (Finset.singleton_inj.mp h)
    have h2f : 2 * f ≤ s := hns hcard hnsd
    have hmt : movedTop hn2 ε = movedOrbit hn2 (ε r₀) := movedTop_of_one hn2 ε r₀ hone
    have hM2 : 2 ≤ movedOrbit hn2 (ε r₀) := two_le_movedOrbit hn2 (h0 r₀) hr₀
    have hs3 : 2 * s ≤ 6 := by
      calc 2 * s ≤ movedOrbit hn2 (ε r₀) * s := Nat.mul_le_mul_right s hM2
        _ = s * movedTop hn2 ε := by rw [hmt, Nat.mul_comm]
        _ ≤ 6 := hmv
    have hf1 : f = 1 := by
      have h1 : 1 ≤ f := r₀.pos
      omega
    exact Or.inl ⟨r₀, j, hone, hεj, hj, hf1⟩
  · exact Or.inr h4
  ·
    exfalso
    subst hf1
    have hcard : (univ.filter fun r : Fin 1 => ε r ≠ ∅).card ≤ 2 :=
      (Finset.card_filter_le _ _).trans (by simp)
    have hnsd : ∃ r, (ε r).image labelStar ≠ ε r := by
      refine ⟨0, ?_⟩
      rw [hεall 0, Finset.image_singleton]
      intro h
      exact c2suar_labelStar_ne_five hn5 j hj (Finset.singleton_inj.mp h)
    have h2f := hns hcard hnsd
    omega
  · exact absurd ⟨hn3, hf1⟩ hnf
  · omega

end CFSG.LocalAnalysis.WeakClosure81
