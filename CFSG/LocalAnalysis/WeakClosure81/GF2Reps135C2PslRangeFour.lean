module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

private lemma c2slr4_exists_const_of_shift_one {f : ℕ} (hf : 0 < f)
    (ε : Fin f → Finset (Fin 4))
    (hrot : ∀ r : Fin f, ε ⟨(r + 1) % f, Nat.mod_lt _ r.pos⟩ = ε r) :
    ∃ r0 : Fin f, ∀ r, ε r = ε r0 := by
  refine ⟨⟨0, hf⟩, ?_⟩
  have key : ∀ k : ℕ, ∀ hk : k < f, ε ⟨k, hk⟩ = ε ⟨0, hf⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact congrArg ε (Fin.ext rfl)
    | succ k ih =>
        intro hk
        have hk' : k < f := by omega
        have hstep := hrot ⟨k, hk'⟩
        have hmod : (k + 1) % f = k + 1 := Nat.mod_eq_of_lt hk
        have hfin :
            (⟨(k + 1) % f, Nat.mod_lt (k + 1) (⟨k, hk'⟩ : Fin f).pos⟩ : Fin f) =
              ⟨k + 1, hk⟩ := Fin.ext hmod
        rw [hfin] at hstep
        rw [hstep, ih hk']
  intro r
  exact key r.val r.isLt

private lemma c2slr4_twelve_le_orbitSize {S : Finset (Fin 4)}
    (h0 : (⟨0, by omega⟩ : Fin 4) ∉ S) (h2 : 2 ≤ S.card) :
    12 ≤ orbitSize S := by
  have hn0 : 0 < (4 : ℕ) := by norm_num
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  have hN := multinomial_lower (b := blocks S) hb hsum hl
  simpa using hN

theorem w135c2_psl_range_four {f s d : ℕ} (hf : 2 ≤ f)
    (hs : 1 ≤ s) (ε : Fin f → Finset (Fin 4))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 4) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d)
    (hrange : (s = 1 ∧ d ≤ 3 * 6) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ 6)) :
    (∃ (r₀ : Fin f) (j : Fin 4), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) = 3) ∧ s = f ∧ s ≤ 3) ∨
      (∃ (r₀ : Fin f) (j : Fin 4), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧ (j : ℕ) = 2 ∧
        s = f ∧ s ≤ 3) ∨
      (f = 2 ∧ s = 1 ∧ ∃ j : Fin 4, ((j : ℕ) = 1 ∨ (j : ℕ) = 3) ∧ ∀ r, ε r = {j}) := by
  classical
  set A : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hA
  have hmemA : ∀ r, r ∈ A ↔ ε r ≠ ∅ := by
    intro r
    rw [hA]
    simp
  have hfpos : 0 < f := by omega
  have hAnonempty : A.Nonempty := by
    obtain ⟨r, hr⟩ := hact
    exact ⟨r, (hmemA r).mpr hr⟩
  rcases hrange with ⟨hs1, hd18⟩ | ⟨hs23, hd6⟩
  ·
    rw [hs1] at hrot
    obtain ⟨r0, hconst⟩ := c2slr4_exists_const_of_shift_one hfpos ε hrot
    have hSne : ε r0 ≠ ∅ := by
      obtain ⟨r, hr⟩ := hact
      rw [hconst r] at hr
      exact hr
    have hne_all : ∀ r, ε r ≠ ∅ := by
      intro r
      rw [hconst r]
      exact hSne
    have hAuniv : A = univ := by
      rw [hA]
      exact Finset.filter_true_of_mem fun r _ => hne_all r
    have hprod : ∏ r ∈ A, orbitSize (ε r) = orbitSize (ε r0) ^ f := by
      rw [hAuniv]
      rw [show (∏ r ∈ (univ : Finset (Fin f)), orbitSize (ε r)) =
          ∏ _r ∈ (univ : Finset (Fin f)), orbitSize (ε r0) from
        Finset.prod_congr rfl fun r _ => congrArg orbitSize (hconst r)]
      rw [Finset.prod_const]
      simp
    have hNf : orbitSize (ε r0) ^ f ≤ d := by
      rw [← hprod]
      exact hlow
    have h4N : 4 ≤ orbitSize (ε r0) :=
      n_le_orbitSize (n := 4) (by norm_num) (h0 r0) hSne
    have hpow : 4 ^ f ≤ 18 := by
      have h1 : 4 ^ f ≤ orbitSize (ε r0) ^ f := Nat.pow_le_pow_left h4N f
      exact le_trans h1 (le_trans hNf hd18)
    have hf2 : f = 2 := by
      by_contra h
      have h3 : 3 ≤ f := by omega
      have h43 : (4 : ℕ) ^ 3 ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
      have : (4 : ℕ) ^ 3 ≤ 18 := le_trans h43 hpow
      norm_num at this
    have hNsq : orbitSize (ε r0) ^ 2 ≤ 18 := by
      rw [hf2] at hNf
      exact le_trans hNf hd18
    have hNle4 : orbitSize (ε r0) ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ orbitSize (ε r0) := by omega
      have h25 : 25 ≤ orbitSize (ε r0) ^ 2 := by
        calc 25 = (5 : ℕ) ^ 2 := by norm_num
          _ ≤ orbitSize (ε r0) ^ 2 := Nat.pow_le_pow_left h5 2
      have : 25 ≤ 18 := le_trans h25 hNsq
      norm_num at this
    have hN4 : orbitSize (ε r0) = 4 := by omega
    have hcard1 : (ε r0).card = 1 := by
      by_contra h
      have h2 : 2 ≤ (ε r0).card := by
        have hpos : 0 < (ε r0).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
        omega
      have h12 := c2slr4_twelve_le_orbitSize (S := ε r0) (h0 r0) h2
      rw [hN4] at h12
      norm_num at h12
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0 r0
      rw [hj, Finset.mem_singleton]
      exact Fin.ext (by simpa using h.symm)
    have hjN : (j : ℕ) ≠ 2 := by
      intro h
      have h6 : (4 : ℕ).choose (j : ℕ) = 4 := by
        rw [← orbitSize_singleton (n := 4) j, ← hj, hN4]
      rw [h] at h6
      exact absurd h6 (by decide)
    have hjlt : (j : ℕ) < 4 := j.isLt
    have hj13 : (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by omega
    right
    right
    exact ⟨hf2, hs1, j, hj13, fun r => by simp [hconst r, hj]⟩
  ·
    have hAle1 : A.card = 1 := by
      by_contra h
      have h2 : 2 ≤ A.card := by
        have hpos : 0 < A.card := Finset.card_pos.mpr hAnonempty
        omega
      have hprod_lb : 4 ^ A.card ≤ ∏ r ∈ A, orbitSize (ε r) := by
        have h := Finset.prod_le_prod (s := A) (f := fun _ => (4 : ℕ))
          (g := fun r => orbitSize (ε r))
          (fun r hr => n_le_orbitSize (n := 4) (by norm_num) (h0 r) ((hmemA r).mp hr))
        rwa [Finset.prod_const] at h
      have h16 : 16 ≤ 4 ^ A.card := by
        have h42 : 4 ^ 2 ≤ 4 ^ A.card := Nat.pow_le_pow_right (by norm_num) h2
        simpa using h42
      have : 16 ≤ d := le_trans h16 (le_trans hprod_lb hlow)
      have : 16 ≤ 6 := le_trans this hd6
      norm_num at this
    obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hAle1
    have hsingle : ∀ r, r ≠ r0 → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hmem : r ∈ A := (hmemA r).mpr hne
      rw [hr0] at hmem
      exact hr (Finset.mem_singleton.mp hmem)
    have hprod_eq : ∏ r ∈ A, orbitSize (ε r) = orbitSize (ε r0) := by
      rw [hr0, Finset.prod_singleton]
    have hNr0 : orbitSize (ε r0) ≤ d := by
      rw [← hprod_eq]
      exact hlow
    have hNr06 : orbitSize (ε r0) ≤ 6 := le_trans hNr0 hd6
    have hSne : ε r0 ≠ ∅ :=
      (hmemA r0).mp (by rw [hr0]; exact Finset.mem_singleton_self r0)
    have hcard1 : (ε r0).card = 1 := by
      by_contra h
      have h2 : 2 ≤ (ε r0).card := by
        have hpos : 0 < (ε r0).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
        omega
      have h12 := c2slr4_twelve_le_orbitSize (S := ε r0) (h0 r0) h2
      have : 12 ≤ 6 := le_trans h12 hNr06
      norm_num at this
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0 r0
      rw [hj, Finset.mem_singleton]
      exact Fin.ext (by simpa using h.symm)
    have hsf : s = f := by
      have hfs : f ≤ s := by
        have := hper
        rw [hAle1, mul_one] at this
        exact this
      have hsf' : s ≤ f := by
        by_contra h
        have hlt : f < s := by omega
        obtain ⟨r, hr⟩ := hmin f hfpos hlt
        have hmod : ((r : ℕ) + f) % f = (r : ℕ) := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
        have hfin :
            (⟨((r : ℕ) + f) % f, Nat.mod_lt ((r : ℕ) + f) r.pos⟩ : Fin f) = r :=
          Fin.ext hmod
        rw [hfin] at hr
        exact hr rfl
      omega
    have hsle3 : s ≤ 3 := by rcases hs23 with h | h <;> omega
    have hjlt : (j : ℕ) < 4 := j.isLt
    by_cases hj2 : (j : ℕ) = 2
    · right
      left
      exact ⟨r0, j, hsingle, hj, hj2, hsf, hsle3⟩
    · left
      exact ⟨r0, j, hsingle, hj, by omega, hsf, hsle3⟩

end CFSG.LocalAnalysis.WeakClosure81
