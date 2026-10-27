module

public import CFSG.LocalAnalysis.StandardType.GGTBJE7Tag
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviOn
public import CFSG.LocalAnalysis.StandardType.GGLangE8Recognition
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGTBJOrdinaryOutside.of_cover {E : ℕ → LargeEvenLabel → Prop}
    (hE : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → ¬ ggTBJExoticTag p lab → E p lab) :
    GGTBJOrdinaryOutside E := by
  refine ⟨?_, ?_⟩ <;>
  · intro G _ _ p B Bs x L D J y K hH hp hmark _
    obtain ⟨lab, hΛ, -, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hmark
    exact absurd (hE p lab hp.out hΛ hP.1.1) hP.1.2

private theorem not_five_dvd_four_pow_sub_one_of_three_dvd {n : ℕ} (h5 : 5 ∣ 4 ^ n - 1)
    (h3 : 3 ∣ 2 ^ n + 1) : False := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    generalize 2 ^ (k + k) = x at h h3
    omega
  · have h : 4 ^ (2 * k + 1) % 5 = 4 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    generalize 4 ^ (2 * k + 1) = x at h h5
    omega

theorem ggTBJOrdinaryLabel_cover {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hX : ¬ ggTBJExoticTag p lab) :
    ((((((((((((((((((((GGRootGenSmallRankLabel p lab ∨ ggTBJFieldTwoLabel p lab ∨
      GGTableBNbrInnerNineClassicalLabel p lab ∨ ggTBJSplitALabel p lab) ∨
      ggTBJUnitaryDvdLabel p lab) ∨ ggTBJUnitarySixLabel p lab) ∨
      ggTBJUnitaryRankThreeLabel p lab) ∨ ggTBJSevenLabel p lab) ∨ ggTBJSpPlusLabel p lab) ∨
      ggTBJEThreeLabel p lab) ∨ ggTBJLinMinusLabel p lab) ∨ ggTBJUniMinusLabel p lab) ∨
      ggTBJSympMinusGeTwoLabel p lab) ∨ ggTBJOrthLabel p lab) ∨ ggTBJSympMinusOneLabel p lab) ∨
      (GGUnitaryCoprimeLabel p lab ∧ 4 ≤ lab.rank)) ∨ ggTBJF4LabelNeTwoThree p lab) ∨
      ggTBJSpRankThreeLabel p lab) ∨ ggTBJTwE6LabelGeFive p lab) ∨ ggTBJTwE6LabelFoldCover p lab) ∨
      ggTBJE6Label p lab) ∨ ggTBJF4Label p lab) ∨ ggTBJTwE6LabelThree p lab) ∨
      ggTBJE7Label p lab ∨ lab.tag = .E8 ∨ (lab.tag = .twE6 ∧ 5 < p ∧ p ∣ 2 ^ lab.n + 1) := by
  obtain ⟨t, r, n⟩ := lab
  by_contra hc
  simp only [not_or, and_assoc] at hc
  obtain ⟨hSmall, -, hNine, hSplitA, hUDvd, hUSix, hURk3, hSeven, hSpPlus, hE3, hLinM, hUniM,
    hSympGe2, hOrth, hSympOne, hUCop, -, hSpRk3, hTwGe5, hTwFold, hE6, hF4, hTwThree, hE7, hE8,
    hLP⟩ := hc
  obtain ⟨hn, hΛt⟩ := hΛ
  replace hn : 1 ≤ n := hn
  by_cases h4 : p ∣ 4 ^ n - 1
  swap
  · refine hE3 ⟨h4, ?_, ?_, ?_⟩
    · rintro ⟨rfl, h | h⟩
      · exact hSeven ⟨rfl, Or.inl h⟩
      · exact hSeven ⟨rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact fun h => hSmall (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact fun h => hSmall (Or.inl ⟨h.1, Or.inl h.2⟩)
  have hq : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := ggLabPhiOneTwo_dvd hp (lab := ⟨t, r, n⟩) h4
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hq with h | h <;> omega
  have hplus : p ∣ 2 ^ n + 1 → ¬ p ∣ 2 ^ n - 1 := by
    intro h1 h2
    have h3 : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h1 h2
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  cases t
  case A =>
    have hr1 : 1 ≤ r := hΛt.1
    by_cases hr2 : r ≤ 2
    · exact hSmall (Or.inl ⟨rfl, by dsimp only; omega⟩)
    rcases hq with hm | hpl
    · exact hSplitA ⟨Or.inl rfl, by dsimp only; omega, hm⟩
    by_cases hr5 : 5 ≤ r
    · exact hLinM ⟨rfl, hr5, hpl⟩
    refine hNine (Or.inl ⟨Or.inl ⟨rfl, by dsimp only; omega⟩, fun j hj hj3 => ?_⟩)
    have hj1 : j = 1 := by
      simp only [reduceCtorEq, if_false] at hj3
      omega
    subst hj1
    simpa only [pow_one] using hplus hpl
  case twA =>
    have hr2 : 2 ≤ r := hΛt.1
    by_cases hr : r = 2
    · exact hSmall (Or.inr (Or.inr (Or.inl ⟨rfl, hr⟩)))
    by_cases hr3 : r = 3
    · subst hr3
      rcases hq with hm | hpl
      · exact hUniM ⟨Or.inl rfl, le_rfl, hm⟩
      · exact hURk3 ⟨Or.inl rfl, rfl, hpl⟩
    rcases hq with hm | hpl
    · exact hUniM ⟨Or.inl rfl, by dsimp only; omega, hm⟩
    by_cases hdr : p ∣ r + 1
    · by_cases h51 : r = 5 ∧ n = 1
      · obtain ⟨rfl, rfl⟩ := h51
        have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpl)
        exact hUSix ⟨rfl, rfl, h3, rfl⟩
      · exact hUDvd ⟨rfl, by dsimp only; omega, h51, hpl, hdr⟩
    · exact hUCop ⟨Or.inl ⟨rfl, hpl, hdr⟩, by omega⟩
  case B =>
    have hr2 : 2 ≤ r := hΛt.1
    by_cases hr : r = 2
    · exact hSmall (Or.inr (Or.inl ⟨Or.inl rfl, hr⟩))
    rcases hq with hm | hpl
    · by_cases hr3 : r = 3
      · exact hSpRk3 ⟨Or.inl rfl, hr3, hm⟩
      · exact hSpPlus ⟨Or.inl rfl, by dsimp only; omega, hm⟩
    · by_cases hn2 : 2 ≤ n
      · exact hSympGe2 ⟨Or.inl rfl, by dsimp only; omega, hpl, hn2⟩
      · exact hSympOne ⟨Or.inl rfl, by dsimp only; omega, hpl, by dsimp only; omega⟩
  case C =>
    have hr2 : 2 ≤ r := hΛt.1
    by_cases hr : r = 2
    · exact hSmall (Or.inr (Or.inl ⟨Or.inr rfl, hr⟩))
    rcases hq with hm | hpl
    · by_cases hr3 : r = 3
      · exact hSpRk3 ⟨Or.inr rfl, hr3, hm⟩
      · exact hSpPlus ⟨Or.inr rfl, by dsimp only; omega, hm⟩
    · by_cases hn2 : 2 ≤ n
      · exact hSympGe2 ⟨Or.inr rfl, by dsimp only; omega, hpl, hn2⟩
      · exact hSympOne ⟨Or.inr rfl, by dsimp only; omega, hpl, by dsimp only; omega⟩
  case D =>
    have hr3 : 3 ≤ r := hΛt
    by_cases hr : r = 3
    · subst hr
      rcases hq with hm | hpl
      · exact hSplitA ⟨Or.inr ⟨rfl, rfl⟩, le_rfl, hm⟩
      refine hNine (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, fun j hj hj3 => ?_⟩)
      have hj1 : j = 1 := by
        simp only [if_true] at hj3
        omega
      subst hj1
      simpa only [pow_one] using hplus hpl
    · exact hOrth ⟨hn, Or.inl rfl, by dsimp only; omega, hq⟩
  case twD =>
    have hr2 : 2 ≤ r := hΛt
    by_cases hr : r = 2
    · exact hSmall (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hr⟩))))
    by_cases hr3 : r = 3
    · subst hr3
      rcases hq with hm | hpl
      · exact hUniM ⟨Or.inr ⟨rfl, rfl⟩, le_rfl, hm⟩
      · exact hURk3 ⟨Or.inr rfl, rfl, hpl⟩
    · exact hOrth ⟨hn, Or.inr rfl, by dsimp only; omega, hq⟩
  case E6 => exact hE6 ⟨rfl, h4⟩
  case E7 => exact hE7 ⟨rfl, h4⟩
  case E8 => exact hE8 rfl
  case F4 => exact hF4 ⟨rfl, h4⟩
  case twE6 =>
    by_cases h3 : p = 3
    · exact hTwThree ⟨⟨rfl, h4⟩, h3⟩
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h h3
      · subst h
        norm_num at hp
      · exact h
    by_cases hL : 5 < p ∧ p ∣ 2 ^ n + 1
    · exact hLP ⟨rfl, hL⟩
    by_cases h3q : 3 ∣ 2 ^ n + 1
    · have hp5' : 5 < p := by
        rcases Nat.eq_or_lt_of_le hp5 with h | h
        · subst h
          exact (not_five_dvd_four_pow_sub_one_of_three_dvd h4 h3q).elim
        · exact h
      exact hTwFold ⟨⟨rfl, h4⟩, hp5', h3q, hq.resolve_right fun h => hL ⟨hp5', h⟩⟩
    · exact hTwGe5 ⟨⟨rfl, h4⟩, hp5, h3q, hL⟩
  all_goals exact hX (by simp [ggTBJExoticTag])

theorem ggTBJOrderRestTwE6Three_of_cells
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGTBJOrderRestSplitAUnitSpRankThreeTwE6GeFiveFoldCoverE6F4TwE6ThreeInput :=
  GGTBJOrdinaryOutside.of_E7 hTCJ hI3 (ggTBJE7LeviL_of_labelRigid hRig)
    (ggTBJE7LeviK_of_labelRigid hRig) <|
  GGTBJOrdinaryOutside.of_proved
    (ggTBJLeftOn_e8 hRig hTCJ ggTCJE8A8Sign_holds (ggTBJE8LeviL_holds hRig))
    (ggTBJNbrOn_e8 hRig hTCJ hI3 hraw hiso ggTCJE8A8Sign_holds (ggTBJE8LeviK_holds hRig)) <|
  GGTBJOrdinaryOutside.of_proved ggTBJLeftOn_twE6_large_prime ggTBJNbrOn_twE6_large_prime <|
  GGTBJOrdinaryOutside.of_cover fun _ _ hp hΛ hX =>
    (ggTBJOrdinaryLabel_cover hp hΛ hX).elim (fun h => Or.inl (Or.inl (Or.inl h))) fun h =>
      h.elim (fun h => Or.inl (Or.inl (Or.inr h))) fun h =>
        h.elim (fun h => Or.inl (Or.inr h)) Or.inr

end CFSG.StandardType

end
