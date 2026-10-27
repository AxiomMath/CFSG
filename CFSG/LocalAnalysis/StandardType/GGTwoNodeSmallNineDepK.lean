module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Check
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.TwoNodeSmall

private theorem pk1_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0 :=
  rfl

private theorem pk1_A8_mod (i j : Fin 8) (hij : i ≠ j) :
    ((CartanMatrix.A 8 i j : ℤ) : ZMod 3) =
      (if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then (2 : ZMod 3) else 0) := by
  rw [pk1_cartanA_entry]
  simp only [hij, if_false]
  split_ifs <;> decide

private theorem pk1_S_card (s : ℕ) (hs : s ≤ 2) (S : Finset (Fin 8))
    (hS : ∀ i : Fin 8, i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + 6) :
    S.card = 6 := by
  interval_cases s
  · have h : S = ({0, 1, 2, 3, 4, 5} : Finset (Fin 8)) := by
      ext i
      rw [hS]
      fin_cases i <;> decide
    rw [h]; decide
  · have h : S = ({1, 2, 3, 4, 5, 6} : Finset (Fin 8)) := by
      ext i
      rw [hS]
      fin_cases i <;> decide
    rw [h]; decide
  · have h : S = ({2, 3, 4, 5, 6, 7} : Finset (Fin 8)) := by
      ext i
      rw [hS]
      fin_cases i <;> decide
    rw [h]; decide

private theorem pk1_card_seven {ι : Type} [Fintype ι] (hcard : Fintype.card ι = 7)
    {n : ℕ} (e : Fin n ≃ ι) : n = 7 := by
  have h := Fintype.card_congr e
  rw [hcard, Fintype.card_fin] at h
  exact h

private theorem pk1_no_equiv {ι : Type} [Fintype ι] (hcard : Fintype.card ι = 7)
    {n : ℕ} (e : Fin n ≃ ι) (hn : n ≠ 7) : False :=
  hn (pk1_card_seven hcard e)

private theorem pk1_A7_ne (i j : Fin 7) :
    (CoxeterMatrix.A 7) i j ≠ 4 ∧ (CoxeterMatrix.A 7) i j ≠ 6 := by
  constructor <;> fin_cases i <;> fin_cases j <;> decide

private theorem pk1_B7_no6 (i j : Fin 7) : (CoxeterMatrix.B 7) i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem pk1_D7_ne (i j : Fin 7) :
    (CFSG.StandardType.ggCoxeterMatrixD 7) i j ≠ 4 ∧
      (CFSG.StandardType.ggCoxeterMatrixD 7) i j ≠ 6 := by
  constructor <;> fin_cases i <;> fin_cases j <;> decide

private theorem pk1_E7_ne (i j : Fin 7) :
    (CoxeterMatrix.E₇) i j ≠ 4 ∧ (CoxeterMatrix.E₇) i j ≠ 6 := by
  constructor <;> fin_cases i <;> fin_cases j <;> decide

private theorem pk1_B7_deg (x : Fin 7) :
    (Finset.univ.filter (fun y : Fin 7 => y ≠ x ∧ (CoxeterMatrix.B 7) x y ≠ 2)).card ≤ 2 := by
  fin_cases x <;> decide

private theorem pk1_no_label6 {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 7) {M : CoxeterMatrix ι}
    (hW : CFSG.StandardType.GGIsWeylMatrix M) (a b : ι) : M a b ≠ 6 := by
  rcases hW with
    ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rw [hA, CoxeterMatrix.reindex_apply]
    have hn : n = 7 := pk1_card_seven hcard e
    subst n
    exact (pk1_A7_ne _ _).2
  · rw [hB, CoxeterMatrix.reindex_apply]
    have hn : n = 7 := pk1_card_seven hcard e
    subst n
    exact pk1_B7_no6 _ _
  · rw [hD, CoxeterMatrix.reindex_apply]
    have hn : n = 7 := pk1_card_seven hcard e
    subst n
    exact (pk1_D7_ne _ _).2
  · intro h
    exact pk1_no_equiv hcard e (by norm_num)
  · rw [hE7, CoxeterMatrix.reindex_apply]
    exact (pk1_E7_ne _ _).2
  · intro h
    exact pk1_no_equiv hcard e (by norm_num)
  · intro h
    exact pk1_no_equiv hcard e (by norm_num)
  · intro h
    exact pk1_no_equiv hcard e (by norm_num)

private theorem pk1_label4_deg {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 7) {M : CoxeterMatrix ι}
    (hW : CFSG.StandardType.GGIsWeylMatrix M) (a b : ι) (hab : M a b = 4) :
    ∀ x : ι, (Finset.univ.filter (fun y => y ≠ x ∧ M x y ≠ 2)).card ≤ 2 := by
  rcases hW with
    ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4⟩ | ⟨e, hG2⟩
  · exfalso
    have hn : n = 7 := pk1_card_seven hcard e
    subst n
    rw [hA, CoxeterMatrix.reindex_apply] at hab
    exact (pk1_A7_ne _ _).1 hab
  · have hn : n = 7 := pk1_card_seven hcard e
    subst n
    intro x
    have hM : ∀ y : ι, M x y = (CoxeterMatrix.B 7) (e.symm x) (e.symm y) := by
      intro y
      rw [hB, CoxeterMatrix.reindex_apply]
    have hcard_eq :
        (Finset.univ.filter (fun y : ι => y ≠ x ∧ M x y ≠ 2)).card =
          (Finset.univ.filter
            (fun k : Fin 7 => k ≠ e.symm x ∧ (CoxeterMatrix.B 7) (e.symm x) k ≠ 2)).card := by
      apply Finset.card_bij (fun y _ => e.symm y)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        refine ⟨?_, ?_⟩
        · intro h
          exact hy.1 (e.symm.injective h)
        · have hy2 : M x y ≠ 2 := hy.2
          rw [hM y] at hy2
          exact hy2
      · intro y1 hy1 y2 hy2 h
        exact e.symm.injective h
      · intro k hk
        refine ⟨e k, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        constructor
        · intro h
          exact hk.1 (by simpa using congrArg e.symm h)
        · rw [hM]
          simpa using hk.2
    rw [hcard_eq]
    exact pk1_B7_deg (e.symm x)
  · exfalso
    have hn : n = 7 := pk1_card_seven hcard e
    subst n
    rw [hD, CoxeterMatrix.reindex_apply] at hab
    exact (pk1_D7_ne _ _).1 hab
  · exact (pk1_no_equiv hcard e (by norm_num)).elim
  · exfalso
    rw [hE7, CoxeterMatrix.reindex_apply] at hab
    exact (pk1_E7_ne _ _).1 hab
  · exact (pk1_no_equiv hcard e (by norm_num)).elim
  · exact (pk1_no_equiv hcard e (by norm_num)).elim
  · exact (pk1_no_equiv hcard e (by norm_num)).elim

private theorem pk1_adj_vals {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : CFSG.StandardType.GGIntCartan M C) {a b : Γ} (hab : a ≠ b)
    (ha : ((C a b : ℤ) : ZMod 3) = 2) (hb : ((C b a : ℤ) : ZMod 3) = 2) :
    C a b = -1 ∧ M a b = 3 := by
  rcases hC.2 a b hab with
    ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, hpr, hn1, hn2⟩ | ⟨hm, hpr, hn1, hn2⟩
  · exfalso
    rw [h1] at ha
    exact absurd ha (by decide)
  · exact ⟨h1, hm⟩
  · exfalso
    have hp : ((C a b : ℤ) : ZMod 3) * ((C b a : ℤ) : ZMod 3) = (2 : ZMod 3) := by
      rw [← Int.cast_mul, hpr]; norm_num
    rw [ha, hb] at hp
    exact absurd hp (by decide)
  · exfalso
    have hp : ((C a b : ℤ) : ZMod 3) * ((C b a : ℤ) : ZMod 3) = (3 : ZMod 3) := by
      rw [← Int.cast_mul, hpr]; norm_num
    rw [ha, hb] at hp
    exact absurd hp (by decide)

private theorem pk1_nonadj_vals {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : CFSG.StandardType.GGIntCartan M C) {a b : Γ} (hab : a ≠ b) (h6 : M a b ≠ 6)
    (ha : ((C a b : ℤ) : ZMod 3) = 0) (hb : ((C b a : ℤ) : ZMod 3) = 0) :
    C a b = 0 ∧ M a b = 2 := by
  rcases hC.2 a b hab with
    ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, hpr, hn1, hn2⟩ | ⟨hm, hpr, hn1, hn2⟩
  · exact ⟨h1, hm⟩
  · exfalso
    rw [h1] at ha
    exact absurd ha (by decide)
  · exfalso
    have hp : ((C a b : ℤ) : ZMod 3) * ((C b a : ℤ) : ZMod 3) = (2 : ZMod 3) := by
      rw [← Int.cast_mul, hpr]; norm_num
    rw [ha, hb] at hp
    exact absurd hp (by decide)
  · exact absurd hm h6

theorem ninedep_kopts (s : ℕ) (hs : s ≤ 2) (S : Finset (Fin 8))
    (hS : ∀ i : Fin 8, i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + 6)
    (MK : CoxeterMatrix (Option ↥S)) (CK : Matrix (Option ↥S) (Option ↥S) ℤ)
    (hW : CFSG.StandardType.GGIsWeylMatrix MK) (hC : CFSG.StandardType.GGIntCartan MK CK)
    (hchain : ∀ i j : ↥S, ((CK (some i) (some j) : ℤ) : ZMod 3) =
      ((CartanMatrix.A 8 (i : Fin 8) (j : Fin 8) : ℤ) : ZMod 3))
    (hself : ((CK none none : ℤ) : ZMod 3) = 2)
    (hc : ∃ c : ↥S, ∀ j : ↥S, CK none (some j) ≠ 0 ↔ j = c) :
    ∃ o ∈ kopts (), ∀ j : ↥S,
      ((CK (some j) none : ℤ) : ZMod 3) = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3) ∧
      ((CK none (some j) : ℤ) : ZMod 3) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3) := by
  obtain ⟨c, hc⟩ := hc
  have hcard : Fintype.card (Option ↥S) = 7 := by
    rw [Fintype.card_option, Fintype.card_coe, pk1_S_card s hs S hS]
  have hadj_entry : ∀ i j : ↥S, i ≠ j →
      ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) →
      CK (some i) (some j) = -1 ∧ MK (some i) (some j) = 3 := by
    intro i j hij h
    have h8 : (i : Fin 8) ≠ (j : Fin 8) := fun he => hij (Subtype.ext he)
    exact pk1_adj_vals hC (by simp [hij])
      (by rw [hchain i j, pk1_A8_mod (i : Fin 8) (j : Fin 8) h8, if_pos h])
      (by rw [hchain j i, pk1_A8_mod (j : Fin 8) (i : Fin 8) (Ne.symm h8), if_pos (Or.symm h)])
  have hnonadj_entry : ∀ i j : ↥S, i ≠ j →
      ¬((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) →
      CK (some i) (some j) = 0 ∧ MK (some i) (some j) = 2 := by
    intro i j hij h
    have h8 : (i : Fin 8) ≠ (j : Fin 8) := fun he => hij (Subtype.ext he)
    exact pk1_nonadj_vals hC (by simp [hij]) (pk1_no_label6 hcard hW (some i) (some j))
      (by rw [hchain i j, pk1_A8_mod (i : Fin 8) (j : Fin 8) h8, if_neg h])
      (by rw [hchain j i, pk1_A8_mod (j : Fin 8) (i : Fin 8) (Ne.symm h8),
        if_neg (fun hh => h (Or.symm hh))])
  set pos : ℕ := (c : ℕ) - s with hposdef
  have hcS : s ≤ (c : ℕ) ∧ (c : ℕ) < s + 6 := (hS (c : Fin 8)).mp c.2
  have hpos_lt : pos < 6 := by
    rw [hposdef]
    omega
  have hposj : ∀ j : ↥S, ((j : ℕ) - s = pos) ↔ j = c := by
    intro j
    constructor
    · intro h
      apply Subtype.ext
      apply Fin.ext
      have hjS := (hS (j : Fin 8)).mp j.2
      rw [hposdef] at h
      omega
    · intro h
      rw [h]
  have hcne : (some c : Option ↥S) ≠ none := by simp
  rcases hC.2 (some c) none hcne with
    ⟨hm2, hx0, hy0⟩ | ⟨hm3, hx1, hy1⟩ | ⟨hm4, hpr, hn1, hn2⟩ | ⟨hm6, hpr, hn1, hn2⟩
  · exact absurd hy0 ((hc c).mpr rfl)
  ·
    refine ⟨(pos, 2, 2), ?_, ?_⟩
    · simp only [kopts, List.mem_append]
      left
      exact List.mem_map.mpr ⟨pos, List.mem_range.mpr hpos_lt, rfl⟩
    · intro j
      constructor
      · by_cases hjc : j = c
        · subst j
          rw [hx1, if_pos ((hposj c).mpr rfl)]
          dsimp only; decide
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hc j).mp hcon)
          have hz : CK (some j) none = 0 :=
            CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
          rw [hz, if_neg hne]
          decide
      · by_cases hjc : j = c
        · subst j
          rw [hy1, if_pos ((hposj c).mpr rfl)]
          dsimp only; decide
        · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
          have hzj : CK none (some j) = 0 := by
            by_contra hcon
            exact hjc ((hc j).mp hcon)
          rw [hzj, if_neg hne]
          decide
  ·
    have hcases : (CK (some c) none = -1 ∧ CK none (some c) = -2) ∨
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
    have hend : pos = 0 ∨ pos = 5 := by
      by_contra hne
      rw [not_or] at hne
      obtain ⟨hne0, hne5⟩ := hne
      have hdeg := (pk1_label4_deg hcard hW (some c) none hm4) (some c)
      have hc1lt : (c : ℕ) - 1 < 8 := by omega
      have hc1mem : s ≤ (c : ℕ) - 1 ∧ (c : ℕ) - 1 < s + 6 := by omega
      let c1 : ↥S := ⟨⟨(c : ℕ) - 1, hc1lt⟩, (hS ⟨(c : ℕ) - 1, hc1lt⟩).mpr hc1mem⟩
      have hc2lt : (c : ℕ) + 1 < 8 := by omega
      have hc2mem : s ≤ (c : ℕ) + 1 ∧ (c : ℕ) + 1 < s + 6 := by omega
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
    · refine ⟨(pos, 2, 1), ?_, ?_⟩
      · rcases hend with hp | hp
        · rw [hp]; decide
        · rw [hp]; decide
      · intro j
        constructor
        · by_cases hjc : j = c
          · subst j
            rw [hx, if_pos ((hposj c).mpr rfl)]
            dsimp only; decide
          · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
            have hzj : CK none (some j) = 0 := by
              by_contra hcon
              exact hjc ((hc j).mp hcon)
            have hz : CK (some j) none = 0 :=
              CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
            rw [hz, if_neg hne]
            decide
        · by_cases hjc : j = c
          · subst j
            rw [hy, if_pos ((hposj c).mpr rfl)]
            dsimp only; decide
          · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
            have hzj : CK none (some j) = 0 := by
              by_contra hcon
              exact hjc ((hc j).mp hcon)
            rw [hzj, if_neg hne]
            decide
    · refine ⟨(pos, 1, 2), ?_, ?_⟩
      · rcases hend with hp | hp
        · rw [hp]; decide
        · rw [hp]; decide
      · intro j
        constructor
        · by_cases hjc : j = c
          · subst j
            rw [hx, if_pos ((hposj c).mpr rfl)]
            dsimp only; decide
          · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
            have hzj : CK none (some j) = 0 := by
              by_contra hcon
              exact hjc ((hc j).mp hcon)
            have hz : CK (some j) none = 0 :=
              CFSG.StandardType.GGIntCartan.eq_zero_symm hC (a := some j) (b := none) (by simp) hzj
            rw [hz, if_neg hne]
            decide
        · by_cases hjc : j = c
          · subst j
            rw [hy, if_pos ((hposj c).mpr rfl)]
            dsimp only; decide
          · have hne : (j : ℕ) - s ≠ pos := fun h => hjc ((hposj j).mp h)
            have hzj : CK none (some j) = 0 := by
              by_contra hcon
              exact hjc ((hc j).mp hcon)
            rw [hzj, if_neg hne]
            decide
  · exact absurd hm6 (pk1_no_label6 hcard hW (some c) none)

end CFSG.TwoNodeSmall

