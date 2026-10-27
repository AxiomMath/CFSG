module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateU33
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34AutE8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34ACand

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem aCandLe_two_of_U34 (hK : K_U34AutE8) {X : Type} [Group X] (h : IsU3 X 2) :
    ACandLe X 2 := by
  intro H _ _ hH _ ⟨eH⟩ n hn
  exact aCandidate_le_two_of_aParam_le_two .PSU (aParam_le_two_of_U34 hK) hH
    (LieModel.of_mulEquiv eH.symm h) hn.some

theorem k_U34ACand_of_autE8 (hK : K_U34AutE8) : K_U34ACand :=
  fun _ _ h => aCandLe_two_of_U34 hK h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
