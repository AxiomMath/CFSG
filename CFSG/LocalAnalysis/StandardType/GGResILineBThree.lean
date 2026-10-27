module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGResILineBThreeExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTablePRow_three_BThreeCThree {T : GGResLineJType} (hT : T = .B3 ∨ T = .C3)
    {labJ labX : LargeEvenLabel} (hJ : ggResLineJLabel T labJ)
    (hrow : GGTablePRow 3 labJ labX) :
    ((labJ.tag = .B ∨ labJ.tag = .C) ∧ labJ.rank = 3 ∧
      (labX = ⟨.C, 4, labJ.n⟩ ∨ labX = ⟨.F4, 0, labJ.n⟩)) ∨
    (labJ.tag = .A ∧ (labJ.rank = 5 ∨ labJ.rank = 6) ∧ 3 ∣ 2 ^ labJ.n + 1 ∧
      (labX = ⟨.A, labJ.rank + 2, labJ.n⟩ ∨
        (labJ.rank = 5 ∧ labX = ⟨.E6, 0, labJ.n⟩))) ∨
    (labJ.tag = .twA ∧ (labJ.rank = 5 ∨ labJ.rank = 6) ∧ 3 ∣ 2 ^ labJ.n - 1 ∧
      (labX = ⟨.twA, labJ.rank + 2, labJ.n⟩ ∨
        (labJ.rank = 5 ∧ labX = ⟨.twE6, 0, labJ.n⟩))) ∨
    (labJ.tag = .twD ∧ labJ.rank = 4 ∧
      ((3 ∣ 2 ^ labJ.n - 1 ∧
          (labX = ⟨.twD, 5, labJ.n⟩ ∨ labX = ⟨.twE6, 0, labJ.n⟩)) ∨
        (3 ∣ 2 ^ labJ.n + 1 ∧
          (labX = ⟨.D, 5, labJ.n⟩ ∨ labX = ⟨.E6, 0, labJ.n⟩)))) := by
  have hJ3 : ggResLineJLabel .B3 labJ := by rcases hT with rfl | rfl <;> exact hJ
  have hnot : ∀ n : ℕ, ¬ (3 ∣ 2 ^ n - 1 ∧ 3 ∣ 2 ^ n + 1) := fun n h =>
    not_dvd_two_pow_add_one_of_dvd_sub_one Nat.prime_three (by norm_num) h.1 h.2
  simp only [ggResLineJLabel] at hJ3
  rcases hJ3 with ⟨ht, hr⟩ | ⟨ht, hr, hsign⟩ | ⟨ht, hr, hsign⟩ | ⟨ht, hr⟩
  · refine Or.inl ⟨ht, hr, ?_⟩
    obtain ⟨tJ, rJ, nJ⟩ := labJ
    obtain ⟨tX, rX, nX⟩ := labX
    rcases ht with rfl | rfl <;> subst hr
    all_goals
      simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
      simp at hrow
      simpa [LargeEvenLabel.mk.injEq] using hrow.2
  · refine Or.inr (Or.inl ⟨ht, hr, hsign, ?_⟩)
    obtain ⟨tJ, rJ, nJ⟩ := labJ
    obtain ⟨tX, rX, nX⟩ := labX
    subst ht
    have hnm : ¬ 3 ∣ 2 ^ nJ - 1 := fun hm => hnot nJ ⟨hm, hsign⟩
    rcases hr with rfl | rfl
    · simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
      simp [hnm, hsign] at hrow
      simpa using hrow
    · simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
      simp [hnm, hsign] at hrow
      obtain ⟨rfl, rfl, h⟩ := hrow
      exact Or.inl (by simp [h])
  · refine Or.inr (Or.inr (Or.inl ⟨ht, hr, hsign, ?_⟩))
    obtain ⟨tJ, rJ, nJ⟩ := labJ
    obtain ⟨tX, rX, nX⟩ := labX
    subst ht
    have hnp : ¬ 3 ∣ 2 ^ nJ + 1 := fun hp => hnot nJ ⟨hsign, hp⟩
    rcases hr with rfl | rfl
    · simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
      simp [hnp, hsign] at hrow
      simpa using hrow
    · simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
      simp [hnp, hsign] at hrow
      obtain ⟨rfl, rfl, h⟩ := hrow
      exact Or.inl (by simp [h])
  · refine Or.inr (Or.inr (Or.inr ⟨ht, hr, ?_⟩))
    obtain ⟨tJ, rJ, nJ⟩ := labJ
    obtain ⟨tX, rX, nX⟩ := labX
    subst ht
    subst hr
    simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at hrow
    simp at hrow
    simpa using hrow

theorem ggResILineBThree_C4_card
    (f : ℕ) :
    LargeEvenLabelAll ⟨.C, 4, f⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 4 384 := by
  have hpq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    change 3 ∣ (2 ^ f) ^ 2 - (1 : ℕ) ^ 2
    rw [Nat.sq_sub_sq]
    rcases three_dvd_two_pow_pred_or_succ f with h | h
    · exact dvd_mul_of_dvd_right h _
    · exact dvd_mul_of_dvd_left h _
  have h := KGA.kga_label (p := 3) (f := f) (N := 4) Nat.prime_three (by norm_num)
    (by norm_num) hpq
  exact h

theorem ggResILineBThree_C4
    (labJ : LargeEvenLabel) (f : ℕ) :
    LargeEvenLabelAll ⟨.C, 4, f⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5 :=
  LargeEvenLabelAll.mono
    (fun (R : Type) [Group R] (I F : Set (MulAut R))
        (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
      GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4))
    (ggResILineBThree_C4_card (f := f))

theorem ggResILineBThree_A7 (labJ : LargeEvenLabel) {f : ℕ} (hplus : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.A, 7, f⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  exact LargeEvenLabelAll.mono
    (fun (R : Type) [Group R] (I F : Set (MulAut R))
        (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
      GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4))
    (ggTwSL_label (r := 4) (f := f) (by norm_num) hplus)

theorem ggResILineBThree_twA7
    (labJ : LargeEvenLabel) {f : ℕ} (hf : 1 ≤ f)
    (hminus : 3 ∣ 2 ^ f - 1) :
    LargeEvenLabelAll ⟨.twA, 7, f⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  exact LargeEvenLabelAll.mono
    (fun (R : Type) [Group R] (I F : Set (MulAut R))
        (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
      GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4))
    (ggTwSU_label (r := 4) hf (by norm_num) hminus)

theorem ggResILineBThree_twD5
    (labJ : LargeEvenLabel) {f : ℕ} (hf : 1 ≤ f)
    (hminus : 3 ∣ 2 ^ f - 1) :
    LargeEvenLabelAll ⟨.twD, 5, f⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  exact LargeEvenLabelAll.mono
    (fun (R : Type) [Group R] (I F : Set (MulAut R))
        (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
      GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4))
    (ggTwOm_label (r := 4) hf (by norm_num) (Or.inl hminus))

theorem ggResILineBThree_D5
    (labJ : LargeEvenLabel) {f : ℕ} (hplus : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.D, 5, f⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  exact LargeEvenLabelAll.mono
    (fun (R : Type) [Group R] (I F : Set (MulAut R))
        (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
      GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4))
    (ggTwOmPlus_label (r := 4) (by norm_num) (by decide) hplus)

theorem ggPumpLineAutKnown_BThreeCThree :
    ∀ (T : GGResLineJType), (T = .B3 ∨ T = .C3) →
      ∀ (labJ labX : LargeEvenLabel), ggResLineJLabel T labJ →
        LargeEvenInLambda2 labX → GGTablePRow 3 labJ labX →
        ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1) →
        LargeEvenLabelAll labX fun R _ I _ =>
          GGTorusAutNotDvdSCJ 3 labJ R I (T.rank + 1) T.bad := by
  intro T hT labJ labX hJ hΛX hrow _
  have hrank : T.rank + 1 = 4 := by rcases hT with rfl | rfl <;> rfl
  have hbad : T.bad = 5 := by rcases hT with rfl | rfl <;> rfl
  rw [hrank, hbad]
  have hconv : ∀ {lab : LargeEvenLabel},
      LargeEvenLabelAll lab (fun R _ I _ => GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) →
      LargeEvenLabelAll lab (fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 5) :=
    fun h => LargeEvenLabelAll.mono
      (fun (R : Type) [Group R] (I F : Set (MulAut R))
          (hSC : GGTorusAutCardSC 3 R I 4 (2 ^ 4 * Nat.factorial 4)) =>
        GGTorusAutCardSC.notDvdSCJ hSC (by norm_num : ¬ 5 ∣ 2 ^ 4 * Nat.factorial 4)) h
  rcases ggTablePRow_three_BThreeCThree hT hJ hrow with
      ⟨_, _, hX⟩ | ⟨_, hrankJ, hsign, hX⟩ | ⟨_, hrankJ, hsign, hX⟩ | ⟨_, _, hX⟩
  · rcases hX with hX | hX
    · rw [hX]
      exact ggResILineBThree_C4 labJ labJ.n
    · rw [hX]
      exact ggResILineBThreeExc_F4 labJ
  · rcases hX with hX | ⟨_, hX⟩
    · rcases hrankJ with h5 | h6
      · rw [h5] at hX
        rw [hX]
        simpa using ggResILineBThree_A7 labJ hsign
      · rw [h6] at hX
        rw [hX]
        simpa using hconv (by
          simpa using ggTwSL_label (r := 4) (f := labJ.n) (by norm_num) hsign (ε := 1))
    · have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
      rw [hX]
      exact ggResILineBThreeExc_E6 hf hsign labJ
  · rcases hX with hX | ⟨_, hX⟩
    · rcases hrankJ with h5 | h6
      · rw [h5] at hX
        have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
        rw [hX]
        simpa using ggResILineBThree_twA7 labJ hf hsign
      · rw [h6] at hX
        have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
        rw [hX]
        simpa using hconv (by
          simpa using ggTwSU_label (r := 4) (f := labJ.n) hf (by norm_num) hsign (ε := 1))
    · have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
      rw [hX]
      exact ggResILineBThreeExc_twE6 hf hsign labJ
  · rcases hX with ⟨hminus, hX | hX⟩ | ⟨hplus, hX | hX⟩
    · have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
      rw [hX]
      exact ggResILineBThree_twD5 labJ hf hminus
    · have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
      rw [hX]
      exact ggResILineBThreeExc_twE6 hf hminus labJ
    · rw [hX]
      exact ggResILineBThree_D5 labJ hplus
    · have hf : 1 ≤ labJ.n := by simpa [hX] using hΛX.1
      rw [hX]
      exact ggResILineBThreeExc_E6 hf hplus labJ

end CFSG.StandardType

end
