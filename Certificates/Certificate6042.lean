module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
public import Certificates.Data.Kernel.CoPairMcL
import Certificates.Kernel.CoPair.McL

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.CoPair in
theorem certificate6042 : ∃ (D : CFSG.KC.CoPair.EqData) (VL : Nat),
    CFSG.KC.CoPair.eqOK Native.mclWordA Native.mclWordB Native.seedW1 275 D = true ∧
      CFSG.KC.CoPair.mclVecOK VL D.SA D.SB :=
  ⟨_, _, KernelCoPair.mcl_eq, KernelCoPair.mcl_vec⟩

end Certificates
