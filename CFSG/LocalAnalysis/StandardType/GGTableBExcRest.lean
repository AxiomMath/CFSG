module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Split
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTableBOtherRest4 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBRest3 GGTableBOtherLabel p lab ∧ ¬ GGTableBF4Label p lab ∧
    ¬ GGTableBE7E8LabelNotThree p lab ∧ ¬ TableBExc.GGTableBG2TwB2Label p lab

theorem ggTableBOtherRest4_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRest4 p lab) (hs : LargeEvenSplit p lab) :
    lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der ∨ ((lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3) := by
  obtain ⟨⟨hO, hND⟩, hF4, hE, hG⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hO hND hF4 hE hG hs hlab ⊢
  cases t with
  | A => exact absurd rfl hO.1
  | twA => exact absurd rfl hO.2.1
  | B => exact absurd rfl hO.2.2.1
  | C => exact absurd rfl hO.2.2.2.1
  | D => exact absurd rfl hO.2.2.2.2.1
  | twD => exact absurd rfl hO.2.2.2.2.2
  | E6 => exact Or.inl rfl
  | twE6 => exact Or.inr (Or.inl rfl)
  | triD4 => exact Or.inr (Or.inr (Or.inl rfl))
  | twF4 => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | G2der => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twF4der => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | G2 => exact absurd (Or.inl rfl) hG
  | twB2 => exact absurd (Or.inr rfl) hG
  | B2der =>
    exfalso
    have hn : n = 1 := hlab.2.2
    subst hn
    rcases hs with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp3⟩
    · exact hp.one_lt.ne' (Nat.dvd_one.mp h)
    · exact h trivial
    · rcases h with h | h <;> cases h
    · exact hND (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, rfl⟩))))
  | F4 =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, ?_⟩)))))
    rcases (largeEvenSplit_F4_iff (lab := ⟨.F4, l, n⟩) rfl).mp hs with h | h
    · exact absurd ⟨rfl, h⟩ hF4
    · exact h.2
  | E7 =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), ?_⟩)))))
    rcases (largeEvenSplit_E_iff (lab := ⟨.E7, l, n⟩) (Or.inr (Or.inl rfl))).mp hs with h | h
    · by_contra hp3
      exact hE ⟨Or.inl rfl, h, hp3⟩
    · exact h.2
  | E8 =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), ?_⟩)))))
    rcases (largeEvenSplit_E_iff (lab := ⟨.E8, l, n⟩) (Or.inr (Or.inr rfl))).mp hs with h | h
    · by_contra hp3
      exact hE ⟨Or.inr rfl, h, hp3⟩
    · exact h.2


theorem ggBstarInputOn_other_of_rest4 (h : GGBstarInputOn GGTableBOtherRest4) :
    GGBstarInputOn (GGTableBRest3 GGTableBOtherLabel) := by
  have h1 := ((ggBstarInputOn_F4_split.or ggBstarInputOn_E7E8_notThree).or
    ggBstarInputOn_G2TwB2).or h
  refine GGBstarInputOn.mono_split h1 fun p lab hR _ => ?_
  by_cases hF : GGTableBF4Label p lab
  · exact Or.inl (Or.inl (Or.inl hF))
  · by_cases hE : GGTableBE7E8LabelNotThree p lab
    · exact Or.inl (Or.inl (Or.inr hE))
    · by_cases hG : TableBExc.GGTableBG2TwB2Label p lab
      · exact Or.inl (Or.inr hG)
      · exact Or.inr ⟨hR, hF, hE, hG⟩

theorem ggStdSubPreInputOn_other_of_rest4 (h : GGStdSubPreInputOn GGTableBOtherRest4) :
    GGStdSubPreInputOn (GGTableBRest3 GGTableBOtherLabel) := by
  have h1 := ((ggStdSubPreInputOn_F4_split.or ggStdSubPreInputOn_E7E8_notThree).or
    ggStdSubPreInputOn_G2TwB2).or h
  refine GGStdSubPreInputOn.mono_split h1 fun p lab hR _ => ?_
  by_cases hF : GGTableBF4Label p lab
  · exact Or.inl (Or.inl (Or.inl hF))
  · by_cases hE : GGTableBE7E8LabelNotThree p lab
    · exact Or.inl (Or.inl (Or.inr hE))
    · by_cases hG : TableBExc.GGTableBG2TwB2Label p lab
      · exact Or.inl (Or.inr hG)
      · exact Or.inr ⟨hR, hF, hE, hG⟩

end CFSG.StandardType
