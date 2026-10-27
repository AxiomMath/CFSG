module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

private lemma c2l42r_twelve_le_orbitSize {S : Finset (Fin 4)}
    (h0 : (⟨0, by omega⟩ : Fin 4) ∉ S) (h2 : 2 ≤ S.card) :
    12 ≤ orbitSize S := by
  have hn0 : 0 < (4 : ℕ) := by norm_num
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  have hN := multinomial_lower (b := blocks S) hb hsum hl
  simpa using hN

theorem w135c2_psl_range_l42 {f s d : ℕ} (hf : f = 1) (hs : 1 ≤ s)
    (ε : Fin f → Finset (Fin 4)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin 4) ∉ ε r)
    (hact : ∃ r, ε r ≠ ∅)
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d)
    (hrange : (s = 1 ∧ d ≤ 3 * 7) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ 7)) :
    s = 1 ∧ ((∃ (r₀ : Fin f) (j : Fin 4), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        (j : ℕ) ≠ 0) ∨ (12 ≤ d ∧ d ≤ 21)) := by
  subst hf
  have hs1 : s = 1 := by
    by_contra hne
    have h1s : 1 < s := by omega
    obtain ⟨r, hr⟩ := hmin 1 (by norm_num) h1s
    have hrv : (r : ℕ) = 0 := by
      have := r.isLt
      omega
    refine hr (congrArg ε ?_)
    apply Fin.ext
    simp [hrv, Nat.mod_one]
  have hd21 : d ≤ 21 := by
    rcases hrange with ⟨-, hd⟩ | ⟨hs23, hd7⟩
    · exact hd
    · rcases hs23 with h | h <;> omega
  refine ⟨hs1, ?_⟩
  let r₀ : Fin 1 := ⟨0, by norm_num⟩
  have heq : ∀ r : Fin 1, r = r₀ := by
    intro r
    apply Fin.ext
    have hr := r.isLt
    have hr0 := r₀.isLt
    omega
  have hSne : ε r₀ ≠ ∅ := by
    obtain ⟨r, hr⟩ := hact
    rwa [heq r] at hr
  have hfilter : univ.filter (fun r => ε r ≠ ∅) = {r₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hSne⟩
    · intro r _
      exact heq r
  have hlow' : orbitSize (ε r₀) ≤ d := by
    have h := hlow
    rw [hfilter, Finset.prod_singleton] at h
    exact h
  by_cases hcard : (ε r₀).card = 1
  · left
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0 r₀
      rw [hj, Finset.mem_singleton]
      exact Fin.ext (by simpa using h.symm)
    exact ⟨r₀, j, fun r hr => absurd (heq r) hr, hj, hj0⟩
  · right
    have h2 : 2 ≤ (ε r₀).card := by
      have hpos : 0 < (ε r₀).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
      omega
    exact ⟨le_trans (c2l42r_twelve_le_orbitSize (S := ε r₀) (h0 r₀) h2) hlow', hd21⟩

end CFSG.LocalAnalysis.WeakClosure81
