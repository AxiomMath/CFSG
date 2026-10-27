module

public import CFSG.LocalAnalysis.StandardType.GGTableBExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowE8Five

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGE8ThreeToralRankInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 → GGExcToralRankInput .E8 K 3

@[expose] def GGE7ThreeToralRankInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 → GGExcToralRankInput .E7 K 3

theorem eq_three_or_five_or_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h11 : p < 11) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases p <;> first | omega | exact absurd hp (by decide)


theorem ggE8SmallToralRankInput_of_three (h3 : GGE8ThreeToralRankInput) :
    GGE8SmallToralRankInput := by
  intro K _ _ _ p hp hp2 h11 hpq
  rcases eq_three_or_five_or_seven hp hp2 h11 with rfl | rfl | rfl
  · exact h3 K hpq
  · exact TableBExc.ggExcToralRankInput_E8_five hpq
  · exact TableBExc.ggExcToralRankInput_E8_seven hpq

theorem ggE7SmallToralRankInput_of_three (h3 : GGE7ThreeToralRankInput) :
    GGE7SmallToralRankInput := by
  intro K _ _ _ p hp hp2 h11 hpq
  rcases eq_three_or_five_or_seven hp hp2 h11 with rfl | rfl | rfl
  · exact h3 K hpq
  · exact TableBExc.ggExcToralRankInput_E7_five hpq
  · exact TableBExc.ggExcToralRankInput_E7_seven hpq

theorem ggExcToralRankInput_E8_of_ne_three {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K p := by
  by_cases h11 : p < 11
  · rcases eq_three_or_five_or_seven hp hp2 h11 with rfl | rfl | rfl
    · exact absurd rfl hp3
    · exact TableBExc.ggExcToralRankInput_E8_five hpq
    · exact TableBExc.ggExcToralRankInput_E8_seven hpq
  · exact TableBExc.ggExcToralRankInput_E8_of_eleven_le hp (by omega) hpq

theorem ggExcToralRankInput_E7_of_ne_three {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K p := by
  by_cases h11 : p < 11
  · rcases eq_three_or_five_or_seven hp hp2 h11 with rfl | rfl | rfl
    · exact absurd rfl hp3
    · exact TableBExc.ggExcToralRankInput_E7_five hpq
    · exact TableBExc.ggExcToralRankInput_E7_seven hpq
  · exact TableBExc.ggExcToralRankInput_E7_of_eleven_le hp (by omega) hpq


theorem largeEvenLabelAll_tableB_E8_split {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (h3 : p = 3 → GGE8ThreeToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E8_of_toral htag hlab hp hpn fun K _ _ _ hpq => by
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 rfl K hpq
    · exact ggExcToralRankInput_E8_of_ne_three hp (ne_two_of_dvd_two_pow_sub_one hlab.1 hpn) hp3
        hpq

theorem largeEvenLabelAll_tableB_E7_split {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (h3 : p = 3 → GGE7ThreeToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E7_of_toral htag hlab hp hpn fun K _ _ _ hpq => by
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 rfl K hpq
    · exact ggExcToralRankInput_E7_of_ne_three hp (ne_two_of_dvd_two_pow_sub_one hlab.1 hpn) hp3
        hpq

theorem largeEvenLabelAll_tableB_E7E8_split {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBE7E8Label p lab) (hlab : LargeEvenInLambda2 lab) (hp : p.Prime)
    (h7 : p = 3 → GGE7ThreeToralRankInput) (h8 : p = 3 → GGE8ThreeToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  rcases h.1 with ht | ht
  · exact largeEvenLabelAll_tableB_E7_split ht hlab hp h.2 h7
  · exact largeEvenLabelAll_tableB_E8_split ht hlab hp h.2 h8

@[expose] def GGTableBE7E8LabelNotThree (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3

theorem ggBstarInputOn_E7E8_notThree : GGBstarInputOn GGTableBE7E8LabelNotThree :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8_split ⟨h.1, h.2.1⟩ hlab hp (fun h3 => absurd h3 h.2.2)
      fun h3 => absurd h3 h.2.2).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_E7E8_notThree : GGStdSubPreInputOn GGTableBE7E8LabelNotThree :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8_split ⟨h.1, h.2.1⟩ hlab hp (fun h3 => absurd h3 h.2.2)
      fun h3 => absurd h3 h.2.2).mono fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

theorem ggBstarInputOn_E7E8_split (h7 : GGE7ThreeToralRankInput) (h8 : GGE8ThreeToralRankInput) :
    GGBstarInputOn GGTableBE7E8Label :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8_split h hlab hp (fun _ => h7) fun _ => h8).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_E7E8_split (h7 : GGE7ThreeToralRankInput)
    (h8 : GGE8ThreeToralRankInput) : GGStdSubPreInputOn GGTableBE7E8Label :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8_split h hlab hp (fun _ => h7) fun _ => h8).mono
      fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

end CFSG.StandardType
