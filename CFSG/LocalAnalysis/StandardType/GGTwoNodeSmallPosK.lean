module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosKLemmas

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cellA_kopts (p N : ℕ) [Fact p.Prime] (hc : CFSG.StandardType.lr6SmallCellA p N) (s : ℕ) (hs : s ≤ 2)
    (S : Finset (Fin (N - 1))) (hS : ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3))
    (MK : CoxeterMatrix (Option ↥S)) (CK : Matrix (Option ↥S) (Option ↥S) ℤ)
    (hW : CFSG.StandardType.GGIsWeylMatrix MK) (hC : CFSG.StandardType.GGIntCartan MK CK)
    (hchain : ∀ i j : ↥S, ((CK (some i) (some j) : ℤ) : ZMod p) =
      ((CartanMatrix.A (N - 1) (i : Fin (N - 1)) (j : Fin (N - 1)) : ℤ) : ZMod p))
    (hself : ((CK none none : ℤ) : ZMod p) = 2) (hc' : ∃ c : ↥S, ∀ j : ↥S, CK none (some j) ≠ 0 ↔ j = c) :
    ∃ o ∈ posOpts p N, ∀ j : ↥S,
      ((CK (some j) none : ℤ) : ZMod p) = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p) ∧
      ((CK none (some j) : ℤ) : ZMod p) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p) := by
  obtain ⟨c, hcatt⟩ := hc'
  have hp3 : 3 ≤ p := by
    rcases hc with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ <;> omega
  have hN : N = 5 ∨ N = 6 ∨ N = 7 := by
    rcases hc with ⟨-, hN⟩ | ⟨-, hN⟩ | ⟨-, hN⟩
    · exact Or.inl hN
    · exact Or.inr (Or.inl hN)
    · exact Or.inr (Or.inr hN)
  have hp2 : 2 ≤ p := by omega
  have hp1 : 1 ≤ p := by omega
  have hcardS : S.card = N - 3 := pks_S_card s N hs hN S hS
  have hcard : Fintype.card (Option ↥S) = N - 2 := by
    rw [Fintype.card_option, Fintype.card_coe, hcardS]
    rcases hN with rfl | rfl | rfl <;> norm_num
  have hc3 : 3 ≤ N - 2 := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hc5 : N - 2 ≤ 5 := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hno6 : ∀ a b : Option ↥S, MK a b ≠ 6 := fun a b =>
    pks_no_label6 (N - 2) hcard hc3 hc5 hW a b
  have hadj_entry : ∀ i j : ↥S, i ≠ j →
      ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) →
      CK (some i) (some j) = -1 ∧ MK (some i) (some j) = 3 := by
    intro i j hij h
    have hij' : (i : Fin (N - 1)) ≠ (j : Fin (N - 1)) := fun he => hij (Subtype.ext he)
    have hres : ((CK (some i) (some j) : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
      rw [hchain i j, pks_AN_mod p N (i : Fin (N - 1)) (j : Fin (N - 1)) hij', if_pos h]
    have hres' : ((CK (some j) (some i) : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
      rw [hchain j i, pks_AN_mod p N (j : Fin (N - 1)) (i : Fin (N - 1)) (Ne.symm hij'),
        if_pos (Or.symm h)]
    exact pks_adj_vals p hp3 hC (by simp [hij]) hres hres'
  have hnonadj_entry : ∀ i j : ↥S, i ≠ j →
      ¬((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) →
      CK (some i) (some j) = 0 ∧ MK (some i) (some j) = 2 := by
    intro i j hij h
    have hij' : (i : Fin (N - 1)) ≠ (j : Fin (N - 1)) := fun he => hij (Subtype.ext he)
    have hres : ((CK (some i) (some j) : ℤ) : ZMod p) = 0 := by
      rw [hchain i j, pks_AN_mod p N (i : Fin (N - 1)) (j : Fin (N - 1)) hij', if_neg h]
    have hres' : ((CK (some j) (some i) : ℤ) : ZMod p) = 0 := by
      rw [hchain j i, pks_AN_mod p N (j : Fin (N - 1)) (i : Fin (N - 1)) (Ne.symm hij'),
        if_neg (fun hh => h (Or.symm hh))]
    exact pks_nonadj_vals p hp3 hC (by simp [hij]) (hno6 (some i) (some j)) hres hres'
  set pos : ℕ := (c : ℕ) - s with hposdef
  have hcS : s ≤ (c : ℕ) ∧ (c : ℕ) < s + (N - 3) := (hS (c : Fin (N - 1))).mp c.2
  have hN3 : 3 ≤ N := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hpos_lt : pos < N - 3 := by rw [hposdef]; omega
  have hposj : ∀ j : ↥S, ((j : ℕ) - s = pos) ↔ j = c := by
    intro j
    constructor
    · intro h
      apply Subtype.ext
      apply Fin.ext
      have hjS := (hS (j : Fin (N - 1))).mp j.2
      rw [hposdef] at h
      omega
    · intro h; rw [h]
  have hcne : (some c : Option ↥S) ≠ none := by simp
  rcases hC.2 (some c) none hcne with
    ⟨hm2, hx0, hy0⟩ | ⟨hm3, hx1, hy1⟩ | ⟨hm4, hpr, hn1, hn2⟩ | ⟨hm6, hpr, hn1, hn2⟩
  · exact absurd hy0 ((hcatt c).mpr rfl)
  · refine ⟨(pos, p - 1, p - 1), pks_mem_posOpts_simple p N pos hpos_lt, ?_⟩
    intro j
    constructor
    · by_cases hjc : j = c
      · subst j
        rw [hx1, if_pos ((hposj c).mpr rfl), pks_neg_one_cast p hp1]
      · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
        have hzj : CK none (some j) = 0 := by
          by_contra hcon
          exact hjc ((hcatt j).mp hcon)
        have hz : CK (some j) none = 0 :=
          CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
        rw [hz, if_neg hne]
        simp
    · by_cases hjc : j = c
      · subst j
        rw [hy1, if_pos ((hposj c).mpr rfl), pks_neg_one_cast p hp1]
      · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
        have hzj : CK none (some j) = 0 := by
          by_contra hcon
          exact hjc ((hcatt j).mp hcon)
        rw [hzj, if_neg hne]
        simp
  · have hcases : (CK (some c) none = -1 ∧ CK none (some c) = -2) ∨
        (CK (some c) none = -2 ∧ CK none (some c) = -1) := by
      have hxle : CK (some c) none ≤ -1 := by omega
      have hyle : CK none (some c) ≤ -1 := by omega
      have hxge : -2 ≤ CK (some c) none := by
        by_contra h
        push Not at h
        have hx3 : CK (some c) none ≤ -3 := by omega
        have h1 : (0 : ℤ) ≤ -(CK (some c) none) := by omega
        have h2 : (0 : ℤ) ≤ -(CK none (some c)) := by omega
        have hmul : (3 : ℤ) * 1 ≤ (-(CK (some c) none)) * (-(CK none (some c))) :=
          mul_le_mul (by omega : (3 : ℤ) ≤ -(CK (some c) none))
            (by omega : (1 : ℤ) ≤ -(CK none (some c))) (by norm_num) h1
        nlinarith [hpr, hmul]
      have hx21 : CK (some c) none = -1 ∨ CK (some c) none = -2 := by omega
      rcases hx21 with hx | hx
      · left
        refine ⟨hx, ?_⟩
        rw [hx] at hpr
        omega
      · right
        refine ⟨hx, ?_⟩
        rw [hx] at hpr
        omega
    have hend : pos = 0 ∨ pos = N - 4 := by
      by_contra hne
      rw [not_or] at hne
      obtain ⟨hne0, hneN4⟩ := hne
      have hdeg := (pks_label4_deg (N - 2) hcard hc3 hc5 hW (some c) none hm4) (some c)
      have hc1lt : (c : ℕ) - 1 < N - 1 := by omega
      have hc1mem : s ≤ (c : ℕ) - 1 ∧ (c : ℕ) - 1 < s + (N - 3) := by omega
      let c1 : ↥S := ⟨⟨(c : ℕ) - 1, hc1lt⟩, (hS ⟨(c : ℕ) - 1, hc1lt⟩).mpr hc1mem⟩
      have hc2lt : (c : ℕ) + 1 < N - 1 := by omega
      have hc2mem : s ≤ (c : ℕ) + 1 ∧ (c : ℕ) + 1 < s + (N - 3) := by omega
      let c2 : ↥S := ⟨⟨(c : ℕ) + 1, hc2lt⟩, (hS ⟨(c : ℕ) + 1, hc2lt⟩).mpr hc2mem⟩
      have hc1ne : c1 ≠ c := by
        intro h
        have hh : (c1 : ℕ) = (c : ℕ) := congrArg (fun z : ↥S => (z : ℕ)) h
        simp only [c1] at hh
        omega
      have hc2ne : c2 ≠ c := by
        intro h
        have hh : (c2 : ℕ) = (c : ℕ) := congrArg (fun z : ↥S => (z : ℕ)) h
        simp only [c2] at hh
        omega
      have hc12 : c1 ≠ c2 := by
        intro h
        have hh : (c1 : ℕ) = (c2 : ℕ) := congrArg (fun z : ↥S => (z : ℕ)) h
        simp only [c1, c2] at hh
        omega
      have hM1 : MK (some c) (some c1) = 3 :=
        (hadj_entry c c1 (Ne.symm hc1ne) (Or.inr (by simp only [c1]; omega))).2
      have hM2 : MK (some c) (some c2) = 3 :=
        (hadj_entry c c2 (Ne.symm hc2ne) (Or.inl (by simp only [c2]))).2
      have hsub : ({none, some c1, some c2} : Finset (Option ↥S)) ⊆
          Finset.univ.filter (fun y : Option ↥S => y ≠ some c ∧ MK (some c) y ≠ 2) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hy with rfl | rfl | rfl
        · exact ⟨by simp, by rw [hm4]; norm_num⟩
        · exact ⟨by simp [hc1ne], by rw [hM1]; norm_num⟩
        · exact ⟨by simp [hc2ne], by rw [hM2]; norm_num⟩
      have hcard3 : ({none, some c1, some c2} : Finset (Option ↥S)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp),
          Finset.card_insert_of_notMem (by simpa using hc12),
          Finset.card_singleton]
      have hle := Finset.card_le_card hsub
      omega
    rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · refine ⟨(pos, p - 1, p - 2), pks_mem_posOpts_double_fst p N pos hend, ?_⟩
      intro j
      constructor
      · by_cases hjc : j = c
        · subst j
          rw [hx, if_pos ((hposj c).mpr rfl), pks_neg_one_cast p hp1]
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hcatt j).mp hcon)
          have hz : CK (some j) none = 0 :=
            CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
          rw [hz, if_neg hne]
          simp
      · by_cases hjc : j = c
        · subst j
          rw [hy, if_pos ((hposj c).mpr rfl), pks_neg_two_cast p hp2]
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hcatt j).mp hcon)
          rw [hzj, if_neg hne]
          simp
    · refine ⟨(pos, p - 2, p - 1), pks_mem_posOpts_double_snd p N pos hend, ?_⟩
      intro j
      constructor
      · by_cases hjc : j = c
        · subst j
          rw [hx, if_pos ((hposj c).mpr rfl), pks_neg_two_cast p hp2]
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hcatt j).mp hcon)
          have hz : CK (some j) none = 0 :=
            CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
          rw [hz, if_neg hne]
          simp
      · by_cases hjc : j = c
        · subst j
          rw [hy, if_pos ((hposj c).mpr rfl), pks_neg_one_cast p hp1]
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hcatt j).mp hcon)
          rw [hzj, if_neg hne]
          simp
  · exact absurd hm6 (hno6 (some c) none)

end CFSG.TwoNodeSmall
