module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6ModelCore
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Mathieu.Gen

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KS.SporSch.MOCG

@[expose] def mDerive : List (List Int) := [[-2, 4, 2], [-6, 5, 6], [-5, -2, 5, 2]]

meta def strongMQ : Array (Array Nat) :=
  strongOf 360 (#[0, 2, 3, 4, 6].map fun i => CFSG.EvenSmallLie.OmegaEight.genArrs[i]!)
    [[-2, 4, 2], [-6, 5, 6], [-5, -2, 5, 2]]

meta def baseMQ : Array Nat := #[0, 2, 1, 4, 24, 8]

end CertificateChecks.KernelAE6Tri

#ks_rawchain CertificateChecks.KernelAE6Tri.MQ 360 9 24 CertificateChecks.KernelAE6Tri.strongMQ
  CertificateChecks.KernelAE6Tri.baseMQ 5 CertificateChecks.KernelAE6Tri.mDerive

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KS.Raw

theorem kGensMQ : mgOK MQ.S RG ml = true := by quickRfl

theorem kOrdMQ : Nat.beq (rcnt (MQ.LR 0) * rcnt (MQ.LR 1) * rcnt (MQ.LR 2) * rcnt (MQ.LR 3) *
    rcnt (MQ.LR 4) * rcnt (MQ.LR 5)) 12288 = true := by quickRfl

theorem kGensMQNeg : (!mgOK MQ.S RG (vl.getD 0 [])) = true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
