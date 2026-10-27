module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
public import Certificates.Data.Kernel.CoPairEq
import Certificates.Kernel.CoPair.U62

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.CoPair in
theorem certificate6043 : ∃ D : CFSG.KC.CoPair.EqData,
    CFSG.KC.CoPair.eqOK Native.u62WordA Native.u62WordB Native.seedW2 693 D = true ∧
      (∀ i < 693, CFSG.KC.CoPair.f16 D.SA i = CFSG.Sporadic.Th.Native.ap (CFSG.F4.Native.t46XT ()) i) ∧
      ∀ i < 693, CFSG.KC.CoPair.f16 D.SB i = CFSG.Sporadic.Th.Native.ap (CFSG.F4.Native.t46YT ()) i :=
  ⟨_, KernelCoPair.u62_eq, KernelCoPair.u62_tabs⟩

end Certificates
