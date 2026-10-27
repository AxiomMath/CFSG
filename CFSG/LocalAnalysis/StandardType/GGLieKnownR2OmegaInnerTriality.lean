module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open Matrix TauCeti

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

noncomputable abbrev trialityIsomorphism {F : Type} [Field F] [CharP F 2] :
    ↥(spinGroup (Spin.quadPlus 4 F)) ≃* Om8 F :=
  modelEquiv8 (K := F)

theorem trialityIsomorphism_triSpinAut {F : Type} [Field F] [Finite F] [CharP F 2] :
    MulAut.congr (trialityIsomorphism (F := F))
        (triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) =
      (theta : MulAut (Om8 F)) := by
  rfl

end CFSG.StandardType.LieKnownR2.POmega.Inner
