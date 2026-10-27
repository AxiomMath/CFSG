module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316Leaves
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallPlus

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

section Transfer

variable {G : Type*} [Group G] {L : Subgroup G}

theorem isAltNaturalType_three_of_isOmegaMinusType_zero (h : IsOmegaMinusType L 0) :
    IsAltNaturalType L 3 := by
  obtain ⟨φ, ψ, hψ⟩ := omegaMinusTwo_zero_model
  exact isAltNaturalType_of_isMatrixType φ ψ hψ
    (isMatrixType_of_isOmegaMinusType h)

theorem isAltNaturalType_five_of_isOmegaMinusType_one (h : IsOmegaMinusType L 1) :
    IsAltNaturalType L 5 := by
  obtain ⟨φ, ψ, hψ⟩ := omegaMinusTwo_one_model
  exact isAltNaturalType_of_isMatrixType φ ψ hψ
    (isMatrixType_of_isOmegaMinusType h)

theorem isAltNaturalType_eight_of_isOmegaPlusType_three (h : IsOmegaPlusType L 3) :
    IsAltNaturalType L 8 := by
  obtain ⟨φ, ψ, hψ⟩ := omegaPlusTwo_three_model
  exact isAltNaturalType_of_isMatrixType φ ψ hψ (isMatrixType_of_isOmegaPlusType h)

end Transfer

theorem item316Small_of (hX : Item316ScriptX) (hE : Lit316SolomonEven) (hN : Lit316NonGood) :
    Item316Small := by
  intro G _ _ hsimple hnonab hK hchar he M L hM hL hT
  rcases hT with ⟨m, hm, hplus⟩ | ⟨m, hm, hminus⟩
  · rcases Nat.lt_or_ge m 3 with hlt | hge
    · exact (false_of_isOmegaPlusType_le_two hL.1 (by omega) hplus).elim
    · obtain rfl : m = 3 := by omega
      have h8 : IsAltNaturalType L 8 := isAltNaturalType_eight_of_isOmegaPlusType_three hplus
      by_cases hg : IsSolomonBlock M L
      · obtain ⟨⟨-, -, hab, huniq⟩, hnorm⟩ := hg
        exact hE G hsimple hnonab hK hchar he M L hM hL hab hnorm huniq ⟨8, by norm_num, h8⟩
          (fun t ht h1 => generalizedFitting_centralizer_eq_pCore hchar ht h1)
      · exact hN G hsimple hnonab hK hchar he M L hM hL
          (Or.inl ⟨Or.inl ⟨8, ⟨4, rfl⟩, h8⟩, hg⟩)
  · interval_cases m
    · exact hX G hsimple hnonab hK hchar M L hM hL
        (Or.inr ⟨3, ⟨1, rfl⟩, isAltNaturalType_three_of_isOmegaMinusType_zero hminus⟩)
    · exact hX G hsimple hnonab hK hchar M L hM hL
        (Or.inr ⟨5, ⟨2, rfl⟩, isAltNaturalType_five_of_isOmegaMinusType_one hminus⟩)

end CFSG.RankThree.PartTwo.Sec19
