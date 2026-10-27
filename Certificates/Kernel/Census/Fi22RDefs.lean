module

public import Certificates.Kernel.Sporadic.Fi22.X2069P
public import Certificates.Kernel.Census.Fi22PkU
public import Certificates.Data.Kernel.Census.PackedRootBit
public import Certificates.Data.Kernel.Census.PackedConjF
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Census
open CFSG.ComponentClassification.RankTwoSporadic.Fi22

@[expose] noncomputable def inXK (P : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight P (3510 * 12)) 0,
    bAnd(allN 3510 (fun i => Nat.blt (pg 12 (mask 12) P i) 3510),
      siftK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) CertificateChecks.KernelSpor.Fi22PC.LR
        CertificateChecks.KernelSpor.Fi22PC.TRI CertificateChecks.KernelSpor.Fi22PC.BP 6 0 P))

@[expose] noncomputable def inWK (P : Nat) : Bool :=
  bIf(inXK P, true, inXK (pc 3510 12 fi22UK P))

end CertificateChecks.KernelCensus.Fi22K

end
