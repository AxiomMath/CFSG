module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedAssembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6cL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6rL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K7Rank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedConstruct
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedConstructSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

theorem signedModelK6c_of_isLie811 (hF : SignedK6cFacts) {Y : Type} [Group Y]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) (hfam : fam ≠ .l4) :
    SignedModelK6c Y := by
  obtain ⟨-, -, hX⟩ := h
  cases fam with
  | psp6 =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6c_of_lieModel_psp hF.sp6 hr3 hM
  | omega7 =>
    obtain ⟨-, -, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6c_of_lieModel_pomegaOdd hF.omega7 hr3 hM
  | pomega8m =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6c_of_lieModel_pomegaMinus hF.omega8m hr3 hM
  | l4 => exact absurd rfl hfam
  | l6 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK6c_of_lieModel_psl hF.sl6 (Or.inl rfl) hq hM
    · exact SignedConstructSU.signedModelK6c_of_lieModel_psu hF.su6 (Or.inl rfl) hq hM
  | l7 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK6c_of_lieModel_psl hF.sl7 (Or.inr rfl) hq hM
    · exact SignedConstructSU.signedModelK6c_of_lieModel_psu hF.su7 (Or.inr rfl) hq hM

theorem signedModelK6r_of_isLie811 (hF : SignedK6rFacts) {Y : Type} [Group Y]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) (hfam : fam ≠ .l4) :
    SignedModelK6r Y r := by
  obtain ⟨-, -, hX⟩ := h
  cases fam with
  | psp6 =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6r_of_lieModel_psp hF.sp6 hr3 hM
  | omega7 =>
    obtain ⟨-, -, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6r_of_lieModel_pomegaOdd hF.omega7 hr3 hM
  | pomega8m =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK6r_of_lieModel_pomegaMinus hF.omega8m hr3 hM
  | l4 => exact absurd rfl hfam
  | l6 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK6r_of_lieModel_psl hF.sl6 (Or.inl rfl) hq hM
    · exact SignedConstructSU.signedModelK6r_of_lieModel_psu hF.su6 (Or.inl rfl) hq hM
  | l7 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK6r_of_lieModel_psl hF.sl7 (Or.inr rfl) hq hM
    · exact SignedConstructSU.signedModelK6r_of_lieModel_psu hF.su7 (Or.inr rfl) hq hM

theorem signedModelK7_of_isLie811 (hF : SignedK7Facts) {Y : Type} [Group Y]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) (hfam : fam ≠ .l4) :
    SignedModelK7 Y fam r f := by
  obtain ⟨-, -, hX⟩ := h
  cases fam with
  | psp6 =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK7_of_lieModel_psp hF.sp6 hr3 hM
  | omega7 =>
    obtain ⟨-, -, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK7_of_lieModel_pomegaOdd hF.omega7 hr3 hM
  | pomega8m =>
    obtain ⟨-, hr3, hM⟩ := hX
    exact SignedConstruct.signedModelK7_of_lieModel_pomegaMinus hF.omega8m hr3 hM
  | l4 => exact absurd rfl hfam
  | l6 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK7_of_lieModel_psl hF.sl6 (Or.inl rfl) (Or.inl rfl) hq hM
    · exact SignedConstructSU.signedModelK7_of_lieModel_psu hF.su6 (Or.inl rfl) (Or.inl rfl) hq hM
  | l7 =>
    obtain ⟨-, ⟨hq, hM⟩ | ⟨hq, hM⟩⟩ := hX
    · exact SignedConstruct.signedModelK7_of_lieModel_psl hF.sl7 (Or.inr rfl) (Or.inr rfl) hq hM
    · exact SignedConstructSU.signedModelK7_of_lieModel_psu hF.su7 (Or.inr rfl) (Or.inr rfl) hq hM

theorem k6c_signed_of_facts
    (hF : SignedK6cFacts) {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) (hfam : fam ≠ .l4) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c :=
  k6c_of_signedModel h (signedModelK6c_of_isLie811 hF h hfam) hA h27

theorem k6r_signed_of_facts
    (hF : SignedK6rFacts) {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) (hr5 : 5 ≤ r) (hfam : fam ≠ .l4) {A : Subgroup Y}
    (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → 2 ≤ CFSG.pRank r (centralizer (X : Set Y))) ∧
    (∀ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c →
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 0, 0]),
        c (Multiplicative.ofAdd ![0, 1, 0])} : Set Y)) ∧
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 1, 1]),
        c (Multiplicative.ofAdd ![0, 0, 1])} : Set Y))) :=
  k6r_of_signedModel h (signedModelK6r_of_isLie811 hF h hfam) hr5 hA h27

theorem k7_signed_of_facts
    (hF : SignedK7Facts) {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) (hfam : fam ≠ .l4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (p ∣ qMinusPi r f → 2 ≤ CFSG.pRank p (centralizer (A : Set Y))) ∧
    (p ∣ qPlusPi r f →
      ((fam = .l6 ∨ fam = .l7) → 2 ≤ CFSG.pRank p (centralizer (A : Set Y))) ∧
      ((fam = .psp6 ∨ fam = .omega7) →
        ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
        ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
          p ∣ Nat.card (centralizer (X : Set Y)))) := by
  have hM := signedModelK7_of_isLie811 hF h hfam
  exact ⟨fun hpq => k7a_of_signedModel h hM hp hp5 hpq hA h27, fun hpq =>
    ⟨fun hl => k7b_lin_of_signedModel h hM hl hp hp5 hpq hA h27,
      fun hd => k7b_dvd_of_signedModel h hM hd hp hp5 hpq hA h27⟩⟩

@[expose] def K7Omega8MinusB : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (r f : ℕ), IsLie811 Y .pomega8m r f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi r f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      ∃ y ∈ centralizer (A : Set Y), orderOf y = p ∧
        ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
          ∃ u ∈ centralizer (X : Set Y), orderOf u = p ∧ u * y = y * u ∧ u ∉ zpowers y

theorem k6c_of_facts
    (hF : SignedK6cFacts) : K6c := by
  intro Y _ _ fam r f h A hA h27
  refine ⟨fun hfam => ?_, fun hfam => k6c_signed_of_facts hF h hfam hA h27⟩
  subst hfam
  exact exists_isSumZeroCoords_of_isLie811_l4 h hA h27

theorem k6r_of_facts
    (hF : SignedK6rFacts) : K6r := by
  intro Y _ _ fam r f h hr5 hl4 A hA h27
  by_cases hfam : fam = .l4
  · subst hfam
    have hf : f ≠ 1 := fun hf => hl4 ⟨rfl, hf⟩
    exact ⟨forall_two_le_pRank_centralizer_of_isLie811_l4 h hr5 hf hA h27,
      fun h' => absurd rfl h',
      fun _ c hc => one_le_pRank_centralizer_plane_of_isLie811_l4 h hr5 hf hA h27 c hc⟩
  · obtain ⟨h1, h2⟩ := k6r_signed_of_facts hF h hr5 hfam hA h27
    exact ⟨h1, fun _ => h2, fun h' => absurd h' hfam⟩

theorem k7_of_facts
    (hF : SignedK7Facts) (hB : K7Omega8MinusB) : K7 := by
  intro Y _ _ fam r f h p hp hp5 _ A hA h27
  refine ⟨fun hpq => ?_, fun hpq => ⟨?_, ?_, ?_, ?_⟩,
    fun hpq => pRank_le_two_of_isLie811_of_not_dvd h hp hp5 hpq⟩
  · by_cases hfam : fam = .l4
    · subst hfam
      exact two_le_pRank_centralizer_of_isLie811_l4 h hp hp5 hA h27 hpq
    · exact (k7_signed_of_facts hF h hfam hp hp5 hA h27).1 hpq
  · intro hl
    have hfam : fam ≠ .l4 := by rcases hl with rfl | rfl <;> decide
    exact ((k7_signed_of_facts hF h hfam hp hp5 hA h27).2 hpq).1 hl
  · rintro rfl
    exact pRank_le_two_of_isLie811_l4 h hp hp5 hpq
  · intro hd
    have hfam : fam ≠ .l4 := by rcases hd with rfl | rfl <;> decide
    obtain ⟨h1, h2⟩ := ((k7_signed_of_facts hF h hfam hp hp5 hA h27).2 hpq).2 hd
    exact ⟨h1, h2, pRank_le_three_of_isLie811_psp6_omega7 h hd hp hp5 hpq⟩
  · rintro rfl
    exact hB Y r f h p hp hp5 hpq A hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
