module

public import Certificates.Data.Kernel.Co1BCount
public import Certificates.Kernel.Co1B.TwistData
public import Certificates.Kernel.Co1B.Data21142
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import Certificates.Kernel.J4Q.AllN
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.Sporadic.Co1Block.Iota

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KC.Loop CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def hpK (c : Nat) : Nat :=
  (List.range 6).foldl
    (fun acc i => if c.testBit i = true then mulK acc (getL oneK TWS (hIdx.getD i 0 - 1)) else acc) oneK

@[expose] noncomputable def cntK (c : Nat) : Bool :=
  Nat.beq (strictN (hpK c) fun H => cnt4 AL42 oneK W0L42 W0AL42 H YP42) (getL 0 CNT42 c)

#j4q_all CFSG.KD.Co1B.SQ42 CertificateChecks.KernelCo1B.cntK 64

end CertificateChecks.KernelCo1B

end
