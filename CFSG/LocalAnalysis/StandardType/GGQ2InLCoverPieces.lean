module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafLin
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafHeart
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafUnitFull
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcVacuous
public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverE7

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQ2InLCoverInput_of_pieces
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hrig : GGLabelRigidInput)
    (hplCl : PlacementInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hsymp : ∀ t : ℕ, InLLeafCases (classicalCatalogue (.symp t)))
    (horth : ∀ (t : ℕ) (δ : Fin 2), InLLeafCases (classicalCatalogue (.orth t δ)))
    (hE7 : InLLeafOrSelCases (excRaw 4)) : GGQ2InLCoverInput := by
  refine ggQ2InLCoverInput_of_halves hLB hP hrig classicalCatalogue excCatalogue
    (placementInput_of_split _ hplCl hplEx (placementInputOn_small _)) ?_ ?_
  · intro k hk
    cases k with
    | lin t ε => exact inLLeafCases_lin t ε
    | symp t => exact hsymp t
    | orth t δ => exact horth t δ
    | unitFull N => exact inLLeafCases_unitFull N
    | unitHeart N => exact inLLeafCases_unitHeart N
    | exceptional m => exact hk.elim
  · intro k hk
    cases k with
    | exceptional m =>
      by_cases hm : m = 4
      · subst hm
        exact inLCoverAtFrame_excRaw_E7 hLB hP hrig hE7
      · exact inLCoverAtFrame_of_leafCases hLB hP hrig (inLLeafCases_excRaw m hm)
    | _ => exact (hk trivial).elim

end CFSG.StandardType

end
