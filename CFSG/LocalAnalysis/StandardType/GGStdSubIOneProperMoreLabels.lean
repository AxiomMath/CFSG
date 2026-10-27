module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneMoreTypeALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1

@[expose] def GGIOneMoreUnitaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ (p ∣ lab.rank + 1 ∨ p = 3)

@[expose] def GGIOneMoreSpTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneMoreOrthPlusTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneMoreTwDThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1 ∧ p = 3

@[expose] def GGIOneMoreOrthMinusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGIOneMoreE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ (p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3))

@[expose] def GGIOneMoreExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧
    ((p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.n) ∨ (lab.n = 1 ∧ p = 3))

@[expose] def GGIOneMoreTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGIOneMoreLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreTypeALabel p lab ∨ GGIOneMoreUnitaryLabel p lab ∨ GGIOneMoreSpTwoLabel p lab ∨
    GGIOneMoreOrthPlusTwoLabel p lab ∨ GGIOneMoreTwDThreeLabel p lab ∨
      GGIOneMoreOrthMinusLabel p lab ∨ GGIOneMoreE6Label p lab ∨ GGIOneMoreExcLabel p lab ∨
        GGIOneMoreTwE6Label p lab

theorem IOneMore.not_dvd_both {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p ∣ 2 ^ n - 1 ∧ p ∣ 2 ^ n + 1) := by
  rintro ⟨h1, h2⟩
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem IOneMore.not_dvd_two_pow_one_sub_one {p n : ℕ} (hp : p.Prime) (hn : n = 1) :
    ¬ p ∣ 2 ^ n - 1 := by
  subst hn
  simpa using hp.ne_one

theorem ggIOneProperRestLabel_iff {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) :
    GGIOneProperRestLabel p lab ↔ GGIOneMoreLabel p lab := by
  obtain ⟨t, l, n⟩ := lab
  have hb := IOneMore.not_dvd_both (n := n) hp hp2
  have h1 := IOneMore.not_dvd_two_pow_one_sub_one (n := n) hp
  have h2 : n = 1 → p = 3 → p ∣ 2 ^ n + 1 := by rintro rfl rfl; norm_num
  cases t <;>
    simp only [GGIOneProperRestLabel, GGIOneUnitaryLabel, GGIOneProperDoneLabel, GGTypeALabel,
      GGReflSpLabel, GGTwoThreeLabel, GGCorFourTwoOrthSplitLabel, GGIOneTwDThreeLabel,
      GGCorFourTwoSmallLabel, TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel,
      GGStdSubSmallVacLabel, GGTableBTwDThreeLabel, GGB2derThreeLabel, GGIOneUnitaryTwoLabel,
      GGIOneExcSplitLabel, GGIOneMoreLabel, GGIOneMoreTypeALabel, GGIOneMoreUnitaryLabel,
      GGIOneMoreSpTwoLabel, GGIOneMoreOrthPlusTwoLabel, GGIOneMoreTwDThreeLabel,
      GGIOneMoreOrthMinusLabel, GGIOneMoreE6Label, GGIOneMoreExcLabel, GGIOneMoreTwE6Label,
      LargeEvenSplit, LargeEvenUntwisted, LargeEvenInLambda2, reduceCtorEq, true_and, false_and,
      and_false, false_or, or_false, or_true, not_true, not_false_eq_true, and_true,
      not_and, not_or, ne_eq, not_not] at hlab hs ⊢
  case A =>
    constructor
    · rintro ⟨ha, hb'⟩
      rcases hs with hs | ⟨hn, hp3'⟩
      · exact ⟨hs, ha hs⟩
      · exact absurd hn (hb' hp3')
    · rintro ⟨ha, hl⟩
      exact ⟨fun _ => hl, fun _ hn => h1 hn ha⟩
  case twA =>
    have hd : p ∣ 2 ^ n + 1 := hs.elim id fun h => h2 h.1 h.2
    constructor
    · rintro ⟨ha, hb'⟩
      have hl : 3 ≤ l := by
        by_contra hl
        exact hb' (by omega) hd
      refine ⟨hl, hd, ?_⟩
      by_contra hc
      push Not at hc
      exact ha hd hc.1 hc.2 hl
    · rintro ⟨hl, -, hc⟩
      refine ⟨fun _ h3 h3' _ => hc.elim h3 h3', fun h => absurd h (by omega)⟩
  case B =>
    constructor
    · intro h
      exact hs.resolve_left h
    · rintro ⟨hn, -⟩
      exact h1 hn
  case C =>
    constructor
    · intro h
      exact hs.resolve_left h
    · rintro ⟨hn, -⟩
      exact h1 hn
  case D =>
    constructor
    · rintro ⟨ha, hb', hc⟩
      rcases (show l = 3 ∨ 4 ≤ l by omega) with hl | hl
      · rcases hs with hs | ⟨hn, hp3'⟩
        · exact absurd hs (ha hl)
        · exact absurd hl (hb' hp3' hn)
      · rcases hs with hs | ⟨hn, hp3'⟩
        · exact absurd hs (hc hl)
        · exact ⟨hl, hn, hp3'⟩
    · rintro ⟨hl, hn, hp3'⟩
      exact ⟨fun h => absurd h (by omega), fun _ _ h => absurd h (by omega), fun _ => h1 hn⟩
  case twD =>
    have hsq : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 → p ∣ (2 ^ n) ^ 2 - 1 := by
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        apply Nat.sub_eq_of_eq_add
        ring
      rw [he]
      rintro (h | h)
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _
    have hs' : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 := by
      rcases hs with h | h | ⟨hn, hp3'⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl (h2 hn hp3')
    constructor
    · rintro ⟨ha, hb', hc, hd⟩
      rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with hl | hl | hl
      · exact absurd (hsq hs') (ha hl)
      · have h3 : p ∣ 2 ^ n + 1 := hs'.resolve_right (hd hl)
        exact Or.inl ⟨hl, h3, hc hl h3⟩
      · exact Or.inr ⟨hl, hs'.resolve_right (hb' hl)⟩
    · rintro (⟨hl, hd, hp3'⟩ | ⟨hl, hd⟩)
      · exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ _ => hp3',
          fun _ h => hb ⟨h, hd⟩⟩
      · exact ⟨fun h => absurd h (by omega), fun _ h => hb ⟨h, hd⟩, fun h => absurd h (by omega),
          fun h => absurd h (by omega)⟩
  case E6 => exact iff_of_true trivial hs
  case E7 =>
    constructor
    · intro h
      rcases hs with hs | hs
      · exact Or.inl ⟨hs, h hs⟩
      · exact Or.inr hs
    · rintro (⟨-, h⟩ | ⟨hn, -⟩) hd
      · exact h
      · exact absurd hd (h1 hn)
  case E8 =>
    constructor
    · intro h
      rcases hs with hs | hs
      · exact Or.inl ⟨hs, h hs⟩
      · exact Or.inr hs
    · rintro (⟨-, h⟩ | ⟨hn, -⟩) hd
      · exact h
      · exact absurd hd (h1 hn)
  case F4 =>
    constructor
    · intro h
      rcases hs with hs | hs
      · exact Or.inl ⟨hs, h hs⟩
      · exact Or.inr hs
    · rintro (⟨-, h⟩ | ⟨hn, -⟩) hd
      · exact h
      · exact absurd hd (h1 hn)
  case twE6 => exact iff_of_true trivial (hs.elim id fun h => h2 h.1 h.2)
  case twF4 => exact iff_of_false (fun h => h.2 h.1) id
  case B2der =>
    refine iff_of_false (fun h => h ?_) id
    rcases hs with hs | ⟨-, hp3'⟩
    · exact absurd hs (h1 hlab.2.2)
    · exact hp3'

theorem GGStdSubIOneProperInputOn.mono_split {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubIOneProperInputOn T)
    (hST : ∀ p lab, p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → LargeEvenSplit p lab →
      S p lab → T p lab) :
    GGStdSubIOneProperInputOn S := by
  intro G _ _ p B Bs x L hT hBs hne hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  obtain ⟨hL, lab, hlab, hraw⟩ := hM
  exact h G p B Bs x L hT hBs hne ⟨hL, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hS, hsp, hP⟩ => ⟨hs, hna, θ, hST p lab hp hp2 hlab hsp hS, hsp, hP⟩)
    hraw⟩

end CFSG.StandardType
