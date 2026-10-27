module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.L34T

open CFSG.GH74.KGroups.L34

@[expose] noncomputable def sevenC : Bool :=
  let l7 := (elemsC QP).filter fun q => orderIsP q 7 [7]
  (elemsC QA).all fun a =>
    decide (a * a ≠ 1) || siftC QP a 0 ||
      l7.any fun q => decide (a * q = q * a) || decide (a * q * a⁻¹ = q⁻¹)

end CFSG.Certificates.Kernel.PkCV.L34T

end
