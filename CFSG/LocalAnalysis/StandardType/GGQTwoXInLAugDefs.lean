module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.StandardType

abbrev GGQTwoXInLAug (n : ℕ) : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3) :=
  LinearMap.ker (∑ i : Fin (n + 1), (LinearMap.proj i : (Fin (n + 1) → ZMod 3) →ₗ[ZMod 3] ZMod 3))

end CFSG.StandardType

end
