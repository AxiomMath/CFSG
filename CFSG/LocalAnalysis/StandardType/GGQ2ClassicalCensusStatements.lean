module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalInsideMoved

public section

namespace CFSG.StandardType.GGQ2Frame

@[expose] def CensusCasesLin : Prop :=
  ∀ (t : ℕ) (ε : Fin 2), CensusCases (classicalCatalogue (.lin t ε))

@[expose] def CensusCasesSymp : Prop :=
  ∀ t : ℕ, CensusCases (classicalCatalogue (.symp t))

@[expose] def CensusCasesOrth : Prop :=
  ∀ (t : ℕ) (δ : Fin 2), CensusCases (classicalCatalogue (.orth t δ))

@[expose] def CensusCasesUnitFull : Prop :=
  ∀ N : ℕ, CensusCases (classicalCatalogue (.unitFull N))

@[expose] def CensusCasesUnitHeart : Prop :=
  ∀ N : ℕ, CensusCases (classicalCatalogue (.unitHeart N))

theorem ambModelAtFrame_classical_of_censusCases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hmov : ∀ k, IsClassical k → RawInsideMoved (classicalCatalogue k))
    (hlin : CensusCasesLin) (hsymp : CensusCasesSymp) (horth : CensusCasesOrth)
    (hunF : CensusCasesUnitFull) (hunH : CensusCasesUnitHeart) :
    ∀ k, IsClassical k → AmbModelAtFrame (classicalCatalogue k) := by
  intro k hk
  refine ambModelAtFrame_of_censusCases hLB hP (hmov k hk) ?_
  cases k with
  | lin t ε => exact hlin t ε
  | symp t => exact hsymp t
  | orth t δ => exact horth t δ
  | unitFull N => exact hunF N
  | unitHeart N => exact hunH N
  | exceptional m => exact absurd hk (by simp [IsClassical])

theorem ambModelAtFrame_classical_of_census (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hlin : CensusCasesLin) (hsymp : CensusCasesSymp) (horth : CensusCasesOrth)
    (hunF : CensusCasesUnitFull) (hunH : CensusCasesUnitHeart) :
    ∀ k, IsClassical k → AmbModelAtFrame (classicalCatalogue k) :=
  ambModelAtFrame_classical_of_censusCases hLB hP (fun k hk => classicalCatalogue_rawInsideMoved k hk)
    hlin hsymp horth hunF hunH

end CFSG.StandardType.GGQ2Frame
