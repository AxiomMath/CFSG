module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGRootGenQTwoQFour
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGRootGenSpOrthSplitAvoid
public import CFSG.LocalAnalysis.StandardType.GGSlDvdRootGenQFour
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenQFour
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenRowNine
public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenQFour
public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenQFour
public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenSixThreeQFour
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenQFour
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenQFour

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenQFourRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenOpenLabel p lab ∧ 2 ≤ lab.n ∧
    (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨
      lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n - 1))

private def GGRootGenQFourRows (p : ℕ) (lab : LargeEvenLabel) (first : Prop) : Prop :=
  first ∨ GGTypeALabelDvd p lab ∨ GGRootGenLinPhiTwoLabel p lab ∨
    GGRootGenUnitarySplitLabel p lab ∨ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n) ∨
    GGRootGenUnitaryDvdLabel p lab ∨ GGRootGenUnitaryDvd63Label p lab ∨
    GGRootGenSympLabel p lab ∨ GGRootGenOrthLabel p lab ∨ GGRootGenSpOrthSplitLabel p lab

private theorem GGInnerDiagOnLabel.mono_label_of_lambda2 {G : Type} [Group G]
    {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}
    (hST : ∀ lab, LargeEvenInLambda2 lab → S p lab → T p lab)
    (h : GGInnerDiagOnLabel S p Bs L) : GGInnerDiagOnLabel T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun R _ I F hP => by
      obtain ⟨hs, hna, θ, hcont⟩ := hP
      exact ⟨hs, hna, θ, ⟨hST lab hlab hcont.1, hcont.2⟩⟩) hraw⟩

private theorem ggRootGenLInputOnQFour_of_notKGAvoidOn {R : ℕ → LargeEvenLabel → Prop}
    (hR : GGRootGenKGAvoidOn R) {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ R p lab)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => R p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ R p lab)))
      (fun lab hlab => (em (R p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_L_of_avoidOn hR hHyp h₁
  · exact h G p B Bs x L D J hHyp hq hN h₂

private theorem ggRootGenNbrInputOnQFour_of_notKGAvoidOn {R : ℕ → LargeEvenLabel → Prop}
    (hR : GGRootGenKGAvoidOn R) {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ R p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => R p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ R p lab)))
      (fun lab hlab => (em (R p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_nbr_of_avoidOn hR hHyp hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

private theorem qfourRestLabel {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hopen : GGRootGenOpenLabel p lab) (hn : 2 ≤ lab.n)
    (hTypeADvd : ¬ GGTypeALabelDvd p lab)
    (hLinPhiTwo : ¬ GGRootGenLinPhiTwoLabel p lab)
    (hUnitarySplit : ¬ GGRootGenUnitarySplitLabel p lab)
    (hUnitaryCoprime : ¬ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n))
    (hUnitaryDvd : ¬ GGRootGenUnitaryDvdLabel p lab)
    (hUnitaryDvd63 : ¬ GGRootGenUnitaryDvd63Label p lab)
    (hSymp : ¬ GGRootGenSympLabel p lab) (hOrth : ¬ GGRootGenOrthLabel p lab)
    (hSpOrthSplit : ¬ GGRootGenSpOrthSplitLabel p lab) :
    GGRootGenQFourRestLabel p lab := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn
  have hphi : p ∣ 4 ^ n - 1 := hopen.1
  have hTA : ¬ GGTypeALabel p ⟨t, l, n⟩ := hopen.2
  have h4fac : 4 ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    have hpow : 4 ^ n = (2 ^ n) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    rw [hpow, hsq, mul_comm]
  have hsplit : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    have h := hphi
    rw [h4fac] at h
    exact (Nat.Prime.dvd_mul hp).mp h
  cases t
  ·
    rcases hsplit with h1 | h2
    · by_cases hpl : p ∣ l + 1
      · exact (hTypeADvd ⟨rfl, h1, hpl⟩).elim
      · exact (hTA (Or.inl ⟨rfl, h1, hpl⟩)).elim
    · exact (hLinPhiTwo ⟨h2, hn, Or.inl rfl⟩).elim
  ·
    rcases hsplit with h1 | h2
    · exact (hUnitarySplit ⟨h1, Or.inl rfl⟩).elim
    · by_cases hpl : p ∣ l + 1
      · by_cases h63 : l = 5 ∧ p = 3
        · exact (hUnitaryDvd63 ⟨rfl, h2, hn, h63.1, h63.2⟩).elim
        · exact (hUnitaryDvd ⟨rfl, h2, hpl, hn, h63⟩).elim
      · exact (hUnitaryCoprime ⟨Or.inl ⟨rfl, h2, hpl⟩, hn⟩).elim
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    have hl2 : 2 ≤ l := hlab.2.1
    rcases hsplit with h1 | h2
    · by_cases hl3 : 3 ≤ l
      · exact (hSpOrthSplit (Or.inl ⟨h1, Or.inl rfl, hl3⟩)).elim
      · have hl : l = 2 := by omega
        refine ⟨hopen, hn, ?_⟩
        simp [hl, h1]
    · exact (hSymp ⟨h2, hn, Or.inl rfl⟩).elim
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    have hl2 : 2 ≤ l := hlab.2.1
    rcases hsplit with h1 | h2
    · by_cases hl3 : 3 ≤ l
      · exact (hSpOrthSplit (Or.inl ⟨h1, Or.inr rfl, hl3⟩)).elim
      · have hl : l = 2 := by omega
        refine ⟨hopen, hn, ?_⟩
        simp [hl, h1]
    · exact (hSymp ⟨h2, hn, Or.inr rfl⟩).elim
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    have hl3le : 3 ≤ l := hlab.2
    rcases hsplit with h1 | h2
    · by_cases hl3 : l = 3
      · exact (hTA (Or.inr (Or.inl ⟨rfl, hl3, h1⟩))).elim
      · have hl4 : 4 ≤ l := by omega
        exact (hSpOrthSplit (Or.inr ⟨h1, Or.inl rfl, hl4⟩)).elim
    · by_cases hl3 : l = 3
      · exact (hLinPhiTwo ⟨h2, hn, Or.inr ⟨rfl, hl3⟩⟩).elim
      · have hl4 : 4 ≤ l := by omega
        exact (hOrth ⟨h2, hn, Or.inl rfl, hl4⟩).elim
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    have hl2le : 2 ≤ l := hlab.2
    by_cases hl2 : l = 2
    · have hsq : p ∣ (2 ^ n) ^ 2 - 1 := by
        have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
          simpa using Nat.sq_sub_sq (2 ^ n) 1
        rw [hfac]
        rcases hsplit with h1 | h2
        · exact dvd_mul_of_dvd_right h1 (2 ^ n + 1)
        · exact dvd_mul_of_dvd_left h2 (2 ^ n - 1)
      exact (hTA (Or.inr (Or.inr ⟨rfl, hl2, hsq⟩))).elim
    · have hl3le : 3 ≤ l := by omega
      rcases hsplit with h1 | h2
      · by_cases hl3 : l = 3
        · exact (hUnitarySplit ⟨h1, Or.inr ⟨rfl, hl3⟩⟩).elim
        · have hl4 : 4 ≤ l := by omega
          exact (hSpOrthSplit (Or.inr ⟨h1, Or.inr rfl, hl4⟩)).elim
      · by_cases hl3 : l = 3
        · exact (hUnitaryCoprime ⟨Or.inr ⟨rfl, hl3, h2⟩, hn⟩).elim
        · have hl4 : 4 ≤ l := by omega
          exact (hOrth ⟨h2, hn, Or.inr rfl, hl4⟩).elim
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    exact ⟨hopen, hn, by simp⟩
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    omega
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    omega
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hn1⟩ := hlab.2
    omega

theorem ggRootGenLInputOnQFour_of_rest
    (hRig : GGLabelRigidInput)
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenQFourRestLabel p lab ∧ ¬ X p lab) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  refine ggRootGenLInputOnQFour_of_notQTwo hRig ?_
  refine ggRootGenLInputOnQFour_of_notTypeADvd ?_
  refine ggRootGenLInputOnQFour_of_notLinPhiTwo ?_
  refine ggRootGenLInputOnQFour_of_notUnitarySplit ?_
  refine ggRootGenLInputOnQFour_of_notUnitaryCoprime ?_
  refine ggRootGenLInputOnQFour_of_notUnitaryDvd ?_
  refine ggRootGenLInputOnQFour_of_notUnitaryDvd63 ?_
  refine ggRootGenLInputOnQFour_of_notSymp ?_
  refine ggRootGenLInputOnQFour_of_notKGAvoidOn ggRootGenKGAvoidOn_orth ?_
  refine ggRootGenLInputOnQFour_of_notKGAvoidOn ggRootGenKGAvoidOn_spOrthSplit ?_
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hp : p.Prime := hHyp.1.tableB_facts.1
  refine h G p B Bs x L D J hHyp hq hN ?_
  refine GGInnerDiagOnLabel.mono_label_of_lambda2 (fun lab hlab hP => ?_) hL
  have hnot : ¬ (X p lab ∨ GGRootGenQFourRows p lab (lab.n < 2)) := by
    intro hrow
    exact hP.2 (by
      simp only [GGRootGenQFourRows, or_assoc] at hrow ⊢
      exact hrow)
  obtain ⟨hX, hrows⟩ := not_or.mp hnot
  simp only [GGRootGenQFourRows, not_or] at hrows
  obtain ⟨hnlt, hTypeADvd, hLinPhiTwo, hUnitarySplit, hUnitaryCoprime, hUnitaryDvd,
    hUnitaryDvd63, hSymp, hOrth, hSpOrthSplit⟩ := hrows
  have hn : 2 ≤ lab.n := by omega
  exact ⟨qfourRestLabel hp hlab hP.1 hn hTypeADvd hLinPhiTwo hUnitarySplit hUnitaryCoprime
    hUnitaryDvd hUnitaryDvd63 hSymp hOrth hSpOrthSplit, hX⟩

theorem ggRootGenNbrInputOnQFour_of_rest
    (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenQFourRestLabel p lab ∧ ¬ X p lab) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  refine ggRootGenNbrInputOnQFour_of_notQTwo hRig ?_
  refine ggRootGenNbrInputOnQFour_of_notRowNine ?_
  refine ggRootGenNbrInputOnQFour_of_notTypeADvd ?_
  refine ggRootGenNbrInputOnQFour_of_notLinPhiTwo ?_
  refine ggRootGenNbrInputOnQFour_of_notUnitarySplit ?_
  refine ggRootGenNbrInputOnQFour_of_notUnitaryCoprime ?_
  refine ggRootGenNbrInputOnQFour_of_notUnitaryDvd ?_
  refine ggRootGenNbrInputOnQFour_of_notUnitaryDvd63 hLB hP ?_
  refine ggRootGenNbrInputOnQFour_of_notSymp ?_
  refine ggRootGenNbrInputOnQFour_of_notKGAvoidOn ggRootGenKGAvoidOn_orth ?_
  refine ggRootGenNbrInputOnQFour_of_notKGAvoidOn ggRootGenKGAvoidOn_spOrthSplit ?_
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hL
  have hp : p.Prime := hHyp.1.tableB_facts.1
  refine h G p B Bs x L D J hHyp hq hN y K hnb ?_
  refine GGInnerDiagOnLabel.mono_label_of_lambda2 (fun lab hlab hP => ?_) hL
  have hnot : ¬ (X p lab ∨ GGRootGenQFourRows p lab
      ((lab.n < 2 ∧ ¬ GGRootGenRowNineLabel p lab) ∨ GGRootGenRowNineLabel p lab)) := by
    intro hrow
    exact hP.2 (by
      simp only [GGRootGenQFourRows, or_assoc] at hrow ⊢
      exact hrow)
  obtain ⟨hX, hrows⟩ := not_or.mp hnot
  simp only [GGRootGenQFourRows] at hrows
  obtain ⟨hfirst, hrows⟩ := not_or.mp hrows
  obtain ⟨hnotN2R9, hR9⟩ := not_or.mp hfirst
  obtain ⟨hTypeADvd, hrows⟩ := not_or.mp hrows
  obtain ⟨hLinPhiTwo, hrows⟩ := not_or.mp hrows
  obtain ⟨hUnitarySplit, hrows⟩ := not_or.mp hrows
  obtain ⟨hUnitaryCoprime, hrows⟩ := not_or.mp hrows
  obtain ⟨hUnitaryDvd, hrows⟩ := not_or.mp hrows
  obtain ⟨hUnitaryDvd63, hrows⟩ := not_or.mp hrows
  obtain ⟨hSymp, hrows⟩ := not_or.mp hrows
  obtain ⟨hOrth, hSpOrthSplit⟩ := not_or.mp hrows
  have hn : 2 ≤ lab.n := by
    by_contra hlt
    exact hnotN2R9 ⟨by omega, hR9⟩
  exact ⟨qfourRestLabel hp hlab hP.1 hn hTypeADvd hLinPhiTwo hUnitarySplit hUnitaryCoprime
    hUnitaryDvd hUnitaryDvd63 hSymp hOrth hSpOrthSplit, hX⟩

@[expose] def GGRootGenQFourExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenOpenLabel p lab ∧ 2 ≤ lab.n ∧ GGRootGenExcTag lab

private theorem qfourExcLabel_of_rest {p : ℕ} {lab : LargeEvenLabel}
    (h : GGRootGenQFourRestLabel p lab) (hR : ¬ GGRootGenSmallRankLabel p lab)
    (hE : ¬ GGRootGenSmallExcLabel p lab) : GGRootGenQFourExcLabel p lab := by
  obtain ⟨hO, hn, ht⟩ := h
  refine ⟨hO, hn, ?_⟩
  rcases ht with h | h | h | h | h | h | h | h | h | ⟨hBC, hr, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact (hE (Or.inr (Or.inl h))).elim
  · exact (hE (Or.inl h)).elim
  · exact (hR (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))).elim
  · exact (hE (Or.inr (Or.inr h))).elim
  · exact (hR (Or.inr (Or.inl ⟨hBC, hr⟩))).elim

section Exc

theorem ggRootGenLInputOnQFour_of_excRest (hRig : GGLabelRigidInput)
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenQFourExcLabel p lab ∧ ¬ X p lab) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  refine ggRootGenLInputOnQFour_of_notSmallRank ?_
  refine ggRootGenLInputOnQFour_of_notSmallExc ?_
  refine ggRootGenLInputOnQFour_of_rest hRig ?_
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  refine h G p B Bs x L D J hHyp hq hN (hL.mono_label fun lab hlab => ?_)
  obtain ⟨hrest, hX⟩ := hlab
  simp only [not_or] at hX
  exact ⟨qfourExcLabel_of_rest hrest hX.1.2 hX.2, hX.1.1⟩

theorem ggRootGenNbrInputOnQFour_of_excRest (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenQFourExcLabel p lab ∧ ¬ X p lab) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  refine ggRootGenNbrInputOnQFour_of_notSmallRank ?_
  refine ggRootGenNbrInputOnQFour_of_notSmallExc ?_
  refine ggRootGenNbrInputOnQFour_of_rest hRig hLB hP ?_
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  refine h G p B Bs x L D J hHyp hq hN y K hnb (hK.mono_label fun lab hlab => ?_)
  obtain ⟨hrest, hX⟩ := hlab
  simp only [not_or] at hX
  exact ⟨qfourExcLabel_of_rest hrest hX.1.2 hX.2, hX.1.1⟩

end Exc

end CFSG.StandardType

end
