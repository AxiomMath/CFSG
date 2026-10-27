module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCDefs

public section

namespace CFSG.StandardType

abbrev GGKGCF : Type := GaloisField 2 1

@[expose] noncomputable def ggKGCAFix {V : Type} [AddCommGroup V] [Module GGKGCF V] (k : V ≃ₗ[GGKGCF] V) :
    Submodule GGKGCF V :=
  LinearMap.ker ((k : V →ₗ[GGKGCF] V) - 1)

@[expose] noncomputable def ggKGCAPlane {V : Type} [AddCommGroup V] [Module GGKGCF V] (k : V ≃ₗ[GGKGCF] V) :
    Submodule GGKGCF V :=
  LinearMap.ker ((k : V →ₗ[GGKGCF] V) ^ 2 + (k : V →ₗ[GGKGCF] V) + 1)

end CFSG.StandardType

end
