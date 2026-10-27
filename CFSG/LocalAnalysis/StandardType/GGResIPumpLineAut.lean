module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPumpLineAutNotDvd_C3
    {f : ℕ} (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.C, 3, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  have hpq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rcases three_dvd_two_pow_pred_or_succ f with h | h
    · rw [hfac]
      exact dvd_mul_of_dvd_right h (2 ^ f + 1)
    · rw [hfac]
      exact dvd_mul_of_dvd_left h (2 ^ f - 1)
  exact LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (KGA.kga_label (p := 3) (f := f) (N := 3) Nat.prime_three (by norm_num) (by norm_num) hpq)

theorem ggPumpLineAutNotDvd_A5 {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 5, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 :=
  LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (ggTwSL_label (r := 3) (f := f) (by norm_num) h3)

theorem ggPumpLineAutNotDvd_A6 {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 6, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 :=
  LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (ggTwSL_label (r := 3) (f := f) (by norm_num) h3 (ε := 1) (by norm_num))

theorem ggPumpLineAutNotDvd_twA5
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 :=
  LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (ggTwSU_label (r := 3) (f := f) hf (by norm_num) h3)

theorem ggPumpLineAutNotDvd_twA6
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twA, 6, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 :=
  LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (ggTwSU_label (r := 3) (f := f) hf (by norm_num) h3 (ε := 1) (by norm_num))

theorem ggPumpLineAutNotDvd_twD4
    {f : ℕ} (hf : 1 ≤ f) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twD, 4, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  rcases three_dvd_two_pow_pred_or_succ f with h3 | h3
  · exact LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
      (ggTwOm_label (r := 3) (f := f) hf (by norm_num) (Or.inl h3))
  · exact LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
      (ggTwOm_label (r := 3) (f := f) hf (by norm_num) (Or.inr ⟨by decide, h3⟩))

theorem ggPumpLineAutNotDvd_D3 {f : ℕ} (h3 : 3 ∣ 2 ^ f - 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.D, 3, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_pos rfl] at hQ ⊢
  exact ggPumpLineAutKnown_A3_split_label (f := f) h3 labJ Q hQ

theorem ggPumpLineAutNotDvd_twA3
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twA, 3, n⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 :=
  LargeEvenLabelAll.mono (fun _ _ _ _ h => h.notDvdSCJ (by norm_num))
    (ggPumpLineAutKnown_unitary_four_label (n := n) hn h3)

theorem ggPumpLineAutNotDvd_twD3
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twD, 3, n⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_pos rfl] at hQ ⊢
  exact ggPumpLineAutNotDvd_twA3 hn h3 labJ Q hQ

theorem ggPumpLineAutKnown_A2 :
    ∀ (labJ labX : LargeEvenLabel), ggResLineJLabel .A2 labJ →
      LargeEvenInLambda2 labX → GGTablePRow 3 labJ labX →
      ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1) →
      LargeEvenLabelAll labX fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  intro labJ labX hJ hΛX hrow hOff
  rcases hJ with hJ | hJ
  · rcases ggTablePRow_three_A2_split hJ hrow hΛX with
      hA3 | hC3 | hD3 | htwD4 | htwA5 | hA5A6
    · rw [hA3]
      exact ggPumpLineAutKnown_A3_split_label hJ.2.2 labJ
    · rw [hC3]
      exact ggPumpLineAutNotDvd_C3 labJ
    · rw [hD3]
      exact ggPumpLineAutNotDvd_D3 hJ.2.2 labJ
    · rw [htwD4] at hΛX ⊢
      exact ggPumpLineAutNotDvd_twD4 hΛX.1 labJ
    · obtain ⟨htag, hrank, _hn, h3X⟩ := htwA5
      have hlabX : labX = ⟨.twA, 5, labX.n⟩ := by
        rcases labX with ⟨t, r, n⟩
        simp_all
      rw [hlabX]
      exact ggPumpLineAutNotDvd_twA5 hΛX.1 h3X labJ
    · obtain ⟨htag, hrank, _hn, h3X⟩ := hA5A6
      have hlabX : labX = ⟨.A, labX.rank, labX.n⟩ := by
        rcases labX with ⟨t, r, n⟩
        simp_all
      rw [hlabX]
      rcases hrank with h5 | h6
      · rw [h5]
        exact ggPumpLineAutNotDvd_A5 h3X labJ
      · rw [h6]
        exact ggPumpLineAutNotDvd_A6 h3X labJ
  · rcases ggTablePRow_three_A2_tw_offE6 hJ hrow hΛX hOff with
      htwA3 | hC3 | htwD3 | htwD4
    · rw [htwA3] at hΛX ⊢
      exact ggPumpLineAutNotDvd_twA3 hΛX.1 hJ.2.2 labJ
    · rw [hC3] at hΛX ⊢
      exact ggPumpLineAutNotDvd_C3 labJ
    · rw [htwD3] at hΛX ⊢
      exact ggPumpLineAutNotDvd_twD3 hΛX.1 hJ.2.2 labJ
    · rw [htwD4] at hΛX ⊢
      exact ggPumpLineAutNotDvd_twD4 hΛX.1 labJ

theorem ggPumpLineAutKnown_B2
    (labJ labX : LargeEvenLabel)
    (hJ : ggResLineJLabel .B2 labJ) (hX : LargeEvenInLambda2 labX)
    (hP : GGTablePRow 3 labJ labX)
    (hoff : ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1)) :
    LargeEvenLabelAll labX fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  obtain ⟨tX, rX, nX⟩ := labX
  have hn : 1 ≤ nX := by simpa using hX.1
  rcases ggTablePRow_B2 hJ hX hP with
      hC | ⟨htA, hrA, hnA, h3A⟩ | ⟨htwA, hrwA, hnwA, h3wA⟩ | hD
  · simp only [LargeEvenLabel.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl⟩ := hC
    exact ggPumpLineAutNotDvd_C3 labJ
  · have htA' : tX = .A := by simpa using htA
    have hrA' : rX = 5 ∨ rX = 6 := by simpa using hrA
    have hnA' : nX = labJ.n := by simpa using hnA
    have h3A' : 3 ∣ 2 ^ nX + 1 := by simpa using h3A
    subst tX
    subst nX
    rcases hrA' with rfl | rfl
    · exact ggPumpLineAutNotDvd_A5 h3A' labJ
    · exact ggPumpLineAutNotDvd_A6 h3A' labJ
  · have htwA' : tX = .twA := by simpa using htwA
    have hrwA' : rX = 5 ∨ rX = 6 := by simpa using hrwA
    have hnwA' : nX = labJ.n := by simpa using hnwA
    have h3wA' : 3 ∣ 2 ^ nX - 1 := by simpa using h3wA
    subst tX
    subst nX
    rcases hrwA' with rfl | rfl
    · exact ggPumpLineAutNotDvd_twA5 hn h3wA' labJ
    · exact ggPumpLineAutNotDvd_twA6 hn h3wA' labJ
  · simp only [LargeEvenLabel.mk.injEq] at hD
    obtain ⟨rfl, rfl, rfl⟩ := hD
    exact ggPumpLineAutNotDvd_twD4 hn labJ

end CFSG.StandardType

end
