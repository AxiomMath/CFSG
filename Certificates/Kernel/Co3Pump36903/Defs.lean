module

public import Certificates.Kernel.Co3Pair.Text
public import Certificates.Kernel.Co3Five.Data
public import Certificates.Data.Kernel.Co3TK
public import Certificates.Kernel.Co3T.Data

public section

namespace CertificateChecks.KernelCo3Pump36903

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.Co3TK
open CertificateChecks.KernelCo3T CertificateChecks.KernelCo3Pair CertificateChecks.KernelCo3Five
open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump

@[expose] noncomputable def fuseK (k : Nat) : Bool :=
  Nat.beq k 0 || (Nat.beq tPar[k]! k && (Nat.beq k kA || Nat.beq k kB)) ||
    (Nat.blt tPar[k]! 243 && !Nat.beq tPar[k]! 0 && Nat.blt tGen[k]! 2 &&
      Nat.blt tDep[tPar[k]!]! tDep[k]! &&
      Nat.beq (DE k) (cj 276 9 (PTN.L tGen[k]!) (DE tPar[k]!)))

@[expose] noncomputable def pairK (b c : Nat) : Bool :=
  allN 2 fun i => commPt (PTN.L (b + i)) c &&
    Nat.beq (pw 276 9 (PTN.L (b + i)) 5) (pidn 276 9) && !Nat.beq (PTN.L (b + i)) (pidn 276 9)

@[expose] noncomputable def fiveK (k : Nat) : Bool :=
  !Nat.beq (pw 276 9 (S25.T k) 3) (pidn 276 9) || Nat.beq (S25.T k) (pidn 276 9) ||
    Nat.blt (cntN 125 fun j => commPt (SQ.T j) (S25.T k)) 25

end CertificateChecks.KernelCo3Pump36903

end
