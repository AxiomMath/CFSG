module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Bstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6EndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGTableBE6LabelNotThree (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3

@[expose] def GGTableBOtherRest5 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4 p lab ∧ ¬ GGTableBE6LabelNotThree p lab

theorem ggTableBOtherRest5_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRest5 p lab) (hs : LargeEvenSplit p lab) :
    (lab.tag = .E6 ∧ p = 3) ∨ lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der ∨
        ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3) := by
  obtain ⟨h4, hE6⟩ := h
  rcases ggTableBOtherRest4_cases hp hlab h4 hs with ht | ht | ht | ht | ht | ht | ht
  · refine Or.inl ⟨ht, ?_⟩
    rcases (largeEvenSplit_E_iff (Or.inl ht)).mp hs with hd | hd
    · by_contra hp3
      exact hE6 ⟨ht, hd, hp3⟩
    · exact hd.2
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl ht))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))


namespace TableBExc

theorem recipeChevalleyE6_tableB {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp3 : p ≠ 3)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hT := ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 6, ggTorusLift_E6 hp hp2 hp3 hpq,
    ggBstarBound_E6_of_input hn hK hp hp2 hp3 hpq hT _,
    ggEndNode_E6_of_input hp hp2 hp3 hpq hT⟩

end TableBExc

theorem largeEvenLabelAll_tableB_E6 {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact TableBExc.recipeChevalleyE6_tableB hlab.1 hp hp3 hpn hQ

theorem ggBstarInputOn_E6_notThree : GGBstarInputOn GGTableBE6LabelNotThree :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E6 h.1 hlab hp h.2.2 h.2.1).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_E6_notThree : GGStdSubPreInputOn GGTableBE6LabelNotThree :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E6 h.1 hlab hp h.2.2 h.2.1).mono
      fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

theorem ggBstarInputOn_rest4_of_rest5 (h : GGBstarInputOn GGTableBOtherRest5) :
    GGBstarInputOn GGTableBOtherRest4 := by
  refine GGBstarInputOn.mono_split (ggBstarInputOn_E6_notThree.or h) fun p lab hR _ => ?_
  by_cases hE : GGTableBE6LabelNotThree p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hR, hE⟩

theorem ggStdSubPreInputOn_rest4_of_rest5 (h : GGStdSubPreInputOn GGTableBOtherRest5) :
    GGStdSubPreInputOn GGTableBOtherRest4 := by
  refine GGStdSubPreInputOn.mono_split (ggStdSubPreInputOn_E6_notThree.or h) fun p lab hR _ => ?_
  by_cases hE : GGTableBE6LabelNotThree p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hR, hE⟩


theorem ggBstarInputOn_other_of_rest5 (h : GGBstarInputOn GGTableBOtherRest5) :
    GGBstarInputOn (GGTableBRest3 GGTableBOtherLabel) :=
  ggBstarInputOn_other_of_rest4 (ggBstarInputOn_rest4_of_rest5 h)

theorem ggStdSubPreInputOn_other_of_rest5 (h : GGStdSubPreInputOn GGTableBOtherRest5) :
    GGStdSubPreInputOn (GGTableBRest3 GGTableBOtherLabel) :=
  ggStdSubPreInputOn_other_of_rest4 (ggStdSubPreInputOn_rest4_of_rest5 h)

end CFSG.StandardType
