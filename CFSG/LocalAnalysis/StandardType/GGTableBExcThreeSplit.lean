module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRest

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem largeEvenLabelAll_tableB_E7E8_split_holds {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBE7E8Label p lab) (hlab : LargeEvenInLambda2 lab) (hp : p.Prime) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E7E8_split h hlab hp (fun _ => ggE7ThreeToralRankInput_holds)
    fun _ => ggE8ThreeToralRankInput_holds

theorem ggBstarInputOn_E7E8_split_holds : GGBstarInputOn GGTableBE7E8Label :=
  ggBstarInputOn_E7E8_split ggE7ThreeToralRankInput_holds ggE8ThreeToralRankInput_holds

theorem ggStdSubPreInputOn_E7E8_split_holds : GGStdSubPreInputOn GGTableBE7E8Label :=
  ggStdSubPreInputOn_E7E8_split ggE7ThreeToralRankInput_holds ggE8ThreeToralRankInput_holds

theorem ggBstarInputOn_of_notE7E8Split {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInputOn fun p lab => S p lab ∧ ¬ GGTableBE7E8Label p lab) : GGBstarInputOn S := by
  refine GGBstarInputOn.mono_split (ggBstarInputOn_E7E8_split_holds.or h) fun p lab hS _ => ?_
  by_cases hE : GGTableBE7E8Label p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hS, hE⟩

theorem ggStdSubPreInputOn_of_notE7E8Split {S : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubPreInputOn fun p lab => S p lab ∧ ¬ GGTableBE7E8Label p lab) :
    GGStdSubPreInputOn S := by
  refine GGStdSubPreInputOn.mono_split (ggStdSubPreInputOn_E7E8_split_holds.or h)
    fun p lab hS _ => ?_
  by_cases hE : GGTableBE7E8Label p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hS, hE⟩

theorem ggTableBOtherRest4_cases_of_notE7E8 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRest4 p lab)
    (hE : ¬ GGTableBE7E8Label p lab) (hs : LargeEvenSplit p lab) :
    lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der ∨
        ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1 ∧ p = 3) := by
  rcases ggTableBOtherRest4_cases hp hlab h hs with h1 | h1 | h1 | h1 | h1 | h1 | ⟨ht, hp3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, ?_, hp3⟩)))))
    rcases ht with ht | ht
    · rcases (largeEvenSplit_F4_iff ht).mp hs with hd | hd
      · exact absurd ⟨ht, hd⟩ h.2.1
      · exact hd.1
    · rcases (largeEvenSplit_E_iff (Or.inr ht)).mp hs with hd | hd
      · exact absurd ⟨ht, hd⟩ hE
      · exact hd.1

end CFSG.StandardType
