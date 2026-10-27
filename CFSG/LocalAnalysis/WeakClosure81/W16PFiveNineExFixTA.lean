module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic (LGL)

theorem tautRep_apply (W : Type) [AddCommGroup W] [Module (ZMod 2) W] (u : LGL 2 W) :
    tautRep W u = (u : W →ₗ[ZMod 2] W) :=
  rfl

end CFSG.LocalAnalysis.WeakClosure81

end
