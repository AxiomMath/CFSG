module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSingle
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterMulti
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimSingle
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimAdjoint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset Module
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

private lemma c2sloutran_finrank_single_digit {k : Type} [Field k] [CharP k 2]
    {n f d : ℕ} {ε : Fin f → Finset (Fin n)} {r₀ : Fin f} {j : Fin n}
    (hone : ∀ r, r ≠ r₀ → ε r = ∅) (hj : ε r₀ = {j})
    (hd : d = finrank k (BModel k ε)) : d = n.choose (j : ℕ) := by
  have hcard : ∀ r, (ε r).card ≤ 1 := by
    intro r
    rcases eq_or_ne r r₀ with rfl | hr
    · rw [hj]; simp
    · rw [hone r hr]; simp
  rw [hd, w135c2_finrank_bModel_of_card_le_one (k := k) ε hcard]
  rw [Fintype.prod_eq_single r₀ (fun b hb => by rw [hone b hb]; simp)]
  rw [hj, Finset.prod_singleton]

private lemma c2sloutran_finrank_adjoint_three {k : Type} [Field k] [CharP k 2]
    {d : ℕ} {ε : Fin 1 → Finset (Fin 3)} {r₀ : Fin 1} {a b : Fin 3}
    (ha : (a : ℕ) = 1) (hb : (b : ℕ) = 2) (hε : ε r₀ = {a, b})
    (hd : d = finrank k (BModel k ε)) : d = 8 := by
  rw [hd]
  exact w135c2_finrank_bModel_adjoint_three ε a b ha hb
    (fun r => by rw [Subsingleton.elim r r₀]; exact hε)

theorem w135c2_psl_outer_range {n f s u d : ℕ} {k : Type} [Field k] [CharP k 2] (hn : 2 ≤ n)
    (hs : 1 ≤ s) (hu : 1 ≤ u) (hsu : s * u ≤ 3) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card) (hdvd : s ∣ f)
    (hmv : movedTop hn ε ≤ 4 * u) (hd : d = finrank k (BModel k ε)) :
    (∃ (r₀ : Fin f) (j : Fin n), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n)) ∨
      (n = 2 ∧ f = 3 ∧ s = 3) ∨
      (n = 6 ∧ f = 1 ∧ s = 1 ∧ d = 20) ∨
      (n = 8 ∧ f = 1 ∧ s = 1 ∧ d = 28) ∨
      (n = 4 ∧ f = 1) ∨
      ((s = 1 ∧ d ≤ 3 * gs03Bound .PSL n f) ∨
        ((s = 2 ∨ s = 3) ∧ d ≤ gs03Bound .PSL n f)) := by
  classical
  set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
  have hTmem : ∀ r, r ∈ T ↔ ε r ≠ ∅ := by
    intro r
    rw [hT]
    simp
  have hTpos : 1 ≤ T.card := by
    obtain ⟨r, hr⟩ := hact
    have h := Finset.card_pos.mpr ⟨r, (hTmem r).2 hr⟩
    omega
  rcases eq_or_lt_of_le hTpos with hT1 | hT2
  ·
    have hTcard : T.card = 1 := hT1.symm
    obtain ⟨r₀, hTeq⟩ := Finset.card_eq_one.mp hTcard
    have hr₀ : ε r₀ ≠ ∅ := (hTmem r₀).1 (by rw [hTeq]; exact Finset.mem_singleton_self r₀)
    have hone : ∀ r, r ≠ r₀ → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hmem : r ∈ T := (hTmem r).2 hne
      rw [hTeq] at hmem
      exact hr (Finset.mem_singleton.mp hmem)
    have hper1 : f ≤ s := by
      have h := hper
      rw [hTcard] at h
      simpa using h
    have hsingle := w135c2_psl_outer_single hn hs hu hsu ε h0 r₀ hr₀ hone hper1 hdvd hmv
    rcases hsingle with ⟨j, hj, hnat⟩ | ⟨j, hj, hrange⟩ | ⟨hn6, hf1, hs1, j, hj3, hj⟩
      | ⟨hn8, hf1, hs1, j, hj26, hj⟩ | ⟨hn3, hf1, hs1, a, b, ha1, hb2, hεab⟩
      | ⟨hn4, hf1⟩
    · exact Or.inl ⟨r₀, j, hone, hj, hnat⟩
    · rcases hrange with ⟨hs1, hle⟩ | ⟨hs23, hle⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs1, ?_⟩)))))
        rw [c2sloutran_finrank_single_digit hone hj hd]
        exact hle
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hs23, ?_⟩)))))
        rw [c2sloutran_finrank_single_digit hone hj hd]
        exact hle
    · refine Or.inr (Or.inr (Or.inl ⟨hn6, hf1, hs1, ?_⟩))
      rw [c2sloutran_finrank_single_digit hone hj hd, hj3, hn6]
      norm_num [Nat.choose]
    · rcases hj26 with hj2 | hj6
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hn8, hf1, hs1, ?_⟩)))
        rw [c2sloutran_finrank_single_digit hone hj hd, hj2, hn8]
        norm_num [Nat.choose]
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hn8, hf1, hs1, ?_⟩)))
        rw [c2sloutran_finrank_single_digit hone hj hd, hj6, hn8]
        norm_num [Nat.choose]
    · subst n
      subst f
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hs1, ?_⟩)))))
      have hd8 : d = 8 := c2sloutran_finrank_adjoint_three ha1 hb2 hεab hd
      rw [hd8]
      norm_num [gs03Bound]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn4, hf1⟩))))
  ·
    obtain ⟨r₁, hr₁, r₂, hr₂, hrne⟩ := Finset.one_lt_card.mp hT2
    have h1 : ε r₁ ≠ ∅ := (hTmem r₁).1 hr₁
    have h2 : ε r₂ ≠ ∅ := (hTmem r₂).1 hr₂
    have hmulti := w135c2_psl_outer_multi hn hs hu hsu ε h0 r₁ r₂ hrne h1 h2 hper hdvd hmv
    rcases hmulti with ⟨hn2, hf3, hs3⟩ | ⟨hcard, hrange⟩
    · exact Or.inr (Or.inl ⟨hn2, hf3, hs3⟩)
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      have hd' : d = ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) := by
        rw [hd, w135c2_finrank_bModel_of_card_le_one (k := k) ε hcard]
      rcases hrange with ⟨hs1, hle⟩ | ⟨hs23, hle⟩
      · exact Or.inl ⟨hs1, by rw [hd']; exact hle⟩
      · exact Or.inr ⟨hs23, by rw [hd']; exact hle⟩

end CFSG.LocalAnalysis.WeakClosure81
