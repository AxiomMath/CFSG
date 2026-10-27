module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private lemma c2slr3_orbitSize_classify : ∀ S : Finset (Fin 3),
    (⟨0, by omega⟩ : Fin 3) ∉ S → S ≠ ∅ →
    (S = ({(⟨1, by omega⟩ : Fin 3)} : Finset (Fin 3)) ∧ orbitSize S = 3) ∨
    (S = ({(⟨2, by omega⟩ : Fin 3)} : Finset (Fin 3)) ∧ orbitSize S = 3) ∨
    (S = ({(⟨1, by omega⟩ : Fin 3), (⟨2, by omega⟩ : Fin 3)} : Finset (Fin 3)) ∧
      orbitSize S = 6) := by
  decide +kernel

private lemma c2slr3_const_of_shift_one {f : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin 3))
    (hrot : ∀ r : Fin f, ε ⟨(r + 1) % f, Nat.mod_lt _ r.pos⟩ = ε r) :
    ∀ r : Fin f, ε r = ε ⟨0, hf⟩ := by
  have H : ∀ k, (hk : k < f) → ε ⟨k, hk⟩ = ε ⟨0, hf⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      match k with
      | 0 => exact congrArg ε (Fin.ext rfl)
      | m + 1 =>
        have hm : m < f := by omega
        have hstep : ε (⟨m + 1, hk⟩ : Fin f) = ε (⟨m, hm⟩ : Fin f) := by
          have hfin : (⟨m + 1, hk⟩ : Fin f) =
              ⟨(m + 1) % f, Nat.mod_lt (m + 1) (Fin.pos ⟨m, hm⟩)⟩ := by
            ext
            simp [Nat.mod_eq_of_lt (by omega : m + 1 < f)]
          rw [hfin, hrot ⟨m, hm⟩]
        rw [hstep, ih m (by omega) hm]
  intro r
  exact H r.val r.isLt

theorem w135c2_psl_range_three {f s d : ℕ}
    (hs : 1 ≤ s) (ε : Fin f → Finset (Fin 3))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 3) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d)
    (hrange : (s = 1 ∧ d ≤ 3 * (if f = 1 then 3 else 4)) ∨
      ((s = 2 ∨ s = 3) ∧ d ≤ if f = 1 then 3 else 4)) :
    (∃ (r₀ : Fin f) (j : Fin 3), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧ s = f ∧ s ≤ 3) ∨
      (f = 1 ∧ s = 1 ∧ ∃ a b : Fin 3, (a : ℕ) = 1 ∧ (b : ℕ) = 2 ∧ ∀ r, ε r = {a, b}) ∨
      (f = 2 ∧ s = 1 ∧ ∃ j : Fin 3, ∀ r, ε r = {j}) := by
  classical
  have hfpos : 0 < f := by obtain ⟨r, _⟩ := hact; exact r.pos
  set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
  have hmemT : ∀ r, r ∈ T ↔ ε r ≠ ∅ := by
    intro r; rw [hT]; simp
  have hle_orbit : ∀ r, ε r ≠ ∅ → 3 ≤ orbitSize (ε r) := by
    intro r hr
    have h := n_le_orbitSize (n := 3) (by norm_num) (h0 r) hr
    simpa using h
  have hpow_prod : 3 ^ T.card ≤ ∏ r ∈ T, orbitSize (ε r) :=
    Finset.pow_card_le_prod T (fun r => orbitSize (ε r)) 3
      (fun x hx => hle_orbit x ((hmemT x).1 hx))
  rcases hrange with ⟨hs1, hd1⟩ | ⟨hs23, hd23⟩
  ·
    have hrot1 : ∀ r : Fin f, ε ⟨(r + 1) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
      intro r; simpa [hs1] using hrot r
    have hconst : ∀ r : Fin f, ε r = ε ⟨0, hfpos⟩ :=
      c2slr3_const_of_shift_one hfpos ε hrot1
    set S : Finset (Fin 3) := ε ⟨0, hfpos⟩ with hSdef
    have hconstS : ∀ r : Fin f, ε r = S := by
      intro r; rw [hconst r, hSdef]
    have hSne : S ≠ ∅ := by
      obtain ⟨r₀, hr₀⟩ := hact
      rw [← hconstS r₀]; exact hr₀
    have h0S : (⟨0, by omega⟩ : Fin 3) ∉ S := by
      have h := h0 ⟨0, hfpos⟩
      rw [hconstS ⟨0, hfpos⟩] at h
      exact h
    have hTeq : T = univ := by
      rw [hT]
      apply Finset.filter_true_of_mem
      intro r _
      rw [hconstS r]
      exact hSne
    have hcardT : T.card = f := by rw [hTeq, Finset.card_univ, Fintype.card_fin]
    have hprod_eq : ∏ r ∈ T, orbitSize (ε r) = orbitSize S ^ f := by
      rw [show (∏ r ∈ T, orbitSize (ε r)) = ∏ _r ∈ T, orbitSize S from
        Finset.prod_congr rfl (fun r _ => by rw [hconstS r])]
      rw [Finset.prod_const, hcardT]
    have hpow : orbitSize S ^ f ≤ d := by rw [← hprod_eq]; exact hlow
    have hclass := c2slr3_orbitSize_classify S h0S hSne
    have hfcases : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
    rcases hfcases with hf1 | hf2 | hf3
    ·
      rcases hclass with ⟨hS1, hN1⟩ | ⟨hS2, hN2⟩ | ⟨hS12, hN12⟩
      · left
        refine ⟨⟨0, hfpos⟩, (⟨1, by omega⟩ : Fin 3), ?_, hS1, by omega, by omega⟩
        intro r hr
        exact absurd (Fin.ext (by have := r.isLt
                                  have := (⟨0, hfpos⟩ : Fin f).isLt
                                  omega)) hr
      · left
        refine ⟨⟨0, hfpos⟩, (⟨2, by omega⟩ : Fin 3), ?_, hS2, by omega, by omega⟩
        intro r hr
        exact absurd (Fin.ext (by have := r.isLt
                                  have := (⟨0, hfpos⟩ : Fin f).isLt
                                  omega)) hr
      · right; left
        refine ⟨hf1, hs1, (⟨1, by omega⟩ : Fin 3), (⟨2, by omega⟩ : Fin 3),
          by norm_num, by norm_num, ?_⟩
        intro r
        rw [hconstS r, hS12]
    ·
      rcases hclass with ⟨hS1, hN1⟩ | ⟨hS2, hN2⟩ | ⟨hS12, hN12⟩
      · right; right
        refine ⟨hf2, hs1, (⟨1, by omega⟩ : Fin 3), ?_⟩
        intro r; rw [hconstS r, hS1]
      · right; right
        refine ⟨hf2, hs1, (⟨2, by omega⟩ : Fin 3), ?_⟩
        intro r; rw [hconstS r, hS2]
      · exfalso
        have hd12 : d ≤ 12 := by
          rw [if_neg (by omega : ¬ f = 1)] at hd1
          norm_num at hd1
          exact hd1
        rw [hN12, hf2] at hpow
        norm_num at hpow
        omega
    ·
      exfalso
      have hd12 : d ≤ 12 := by
        rw [if_neg (by omega : ¬ f = 1)] at hd1
        norm_num at hd1
        exact hd1
      have hN3 : 3 ≤ orbitSize S := by
        rcases hclass with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      have h27 : 27 ≤ d := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
          _ ≤ orbitSize S ^ f := Nat.pow_le_pow_left hN3 f
          _ ≤ d := hpow
      omega
  ·
    have hs_gt1 : 1 < s := by rcases hs23 with h | h <;> omega
    have hfne1 : f ≠ 1 := by
      rintro rfl
      obtain ⟨r, hr⟩ := hmin 1 (by norm_num) hs_gt1
      exact hr (congrArg ε (Subsingleton.elim _ _))
    have hf2 : 2 ≤ f := by omega
    have hd4 : d ≤ 4 := by
      rw [if_neg hfne1] at hd23
      exact hd23
    have hpow4 : 3 ^ T.card ≤ d := le_trans hpow_prod hlow
    have hcard1 : T.card = 1 := by
      by_contra hne1
      have hposT : 0 < T.card := by
        rw [Finset.card_pos]
        obtain ⟨r, hr⟩ := hact
        exact ⟨r, (hmemT r).2 hr⟩
      have h2 : 2 ≤ T.card := by omega
      have h9 : 9 ≤ d := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ T.card := Nat.pow_le_pow_right (by norm_num) h2
          _ ≤ d := hpow4
      omega
    obtain ⟨r₀, hTsingle⟩ := Finset.card_eq_one.mp hcard1
    have hr₀T : r₀ ∈ T := by rw [hTsingle]; exact Finset.mem_singleton_self r₀
    have hactive0 : ε r₀ ≠ ∅ := (hmemT r₀).1 hr₀T
    have hother : ∀ r, r ≠ r₀ → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hrT : r ∈ T := (hmemT r).2 hne
      rw [hTsingle, Finset.mem_singleton] at hrT
      exact hr hrT
    have hprod_single : ∏ r ∈ T, orbitSize (ε r) = orbitSize (ε r₀) := by
      rw [hTsingle, Finset.prod_singleton]
    have hNle4 : orbitSize (ε r₀) ≤ 4 := by
      rw [hprod_single] at hlow
      exact le_trans hlow hd4
    have hper' : f ≤ s := by
      rw [hcard1, mul_one] at hper
      exact hper
    have hsf : s ≤ f := by
      by_contra hlt
      have hfs : f < s := by omega
      obtain ⟨r, hr⟩ := hmin f (by omega) hfs
      have hrf : (⟨(r + f) % f, Nat.mod_lt (r + f) r.pos⟩ : Fin f) = r := by
        apply Fin.ext
        show (r.val + f) % f = r.val
        have h := Nat.add_mul_mod_self_left r.val f 1
        simp only [Nat.mul_one, Nat.mod_eq_of_lt r.isLt] at h
        exact h
      exact hr (by rw [hrf])
    have hs_eq_f : s = f := le_antisymm hsf hper'
    have hs_le3 : s ≤ 3 := by rcases hs23 with h | h <;> omega
    rcases c2slr3_orbitSize_classify (ε r₀) (h0 r₀) hactive0 with
      ⟨hS1, hN1⟩ | ⟨hS2, hN2⟩ | ⟨hS12, hN12⟩
    · exact Or.inl ⟨r₀, (⟨1, by omega⟩ : Fin 3), hother, hS1, hs_eq_f, hs_le3⟩
    · exact Or.inl ⟨r₀, (⟨2, by omega⟩ : Fin 3), hother, hS2, hs_eq_f, hs_le3⟩
    · exfalso; omega

end CFSG.LocalAnalysis.WeakClosure81
