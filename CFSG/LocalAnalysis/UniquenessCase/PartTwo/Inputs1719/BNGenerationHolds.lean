module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BNGenerationSmall
public import CFSG.Milestones.ASVolI.I2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ASVolI.ChIJK CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

section Holds


theorem k_19_21_opp_of_list : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    List19_16_5 S → K_19_21_opp S := by
  intro S _ _ hS hL
  rcases hL with (⟨m, h | h | h | h | h | h | h⟩ | ⟨s, -, -, h⟩) | h | h | h
  · obtain ⟨B, N, hBN⟩ := lieModel_has_splitBNPair Nat.prime_two (by decide) h
    exact k_19_21_opp_of_splitBN hBN
  · exact k_19_21_opp_of_classical (Or.inl rfl) h
  · exact k_19_21_opp_of_classical (Or.inr (Or.inr (Or.inl rfl))) h
  · exact k_19_21_opp_of_classical (Or.inr (Or.inl rfl)) h
  · exact k_19_21_opp_of_classical (Or.inl rfl) h
  · exact k_19_21_opp_of_classical (Or.inr (Or.inr (Or.inl rfl))) h
  · exact k_19_21_opp_of_classical (Or.inr (Or.inr (Or.inr rfl))) h
  · exact k_19_21_opp_of_classical (Or.inl rfl) h
  · exact k_19_21_opp_of_alt6 h
  · exact k_19_21_opp_of_u33 h
  · exact k_19_21_opp_of_classical (Or.inr (Or.inl rfl)) h

theorem k_19_21_BN_holds : K_19_21_BN :=
  k_19_21_BN_of_opp k_19_21_opp_of_list

end Holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
