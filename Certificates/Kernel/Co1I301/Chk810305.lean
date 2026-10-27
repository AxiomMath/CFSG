module

public import Certificates.Kernel.Co1I301.Data810305
public import Certificates.Kernel.Co1P.Defs
public import Certificates.Kernel.Co1P.Chk21158
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1I301K
public import Certificates.Data.Kernel.Co1P
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.Sporadic.Co1I301.Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1I301

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KC.Co1I301 CFSG.KLie.CT
  CFSG.KC.M1F2 CFSG.KS.SporSch.M24 CertificateChecks.KernelCo1P CFSG.Sporadic.Co1I301.Native

@[expose] noncomputable def elK (j : Nat) : Nat := getL oneK KI.CDS (j - 1)
@[expose] noncomputable def elIK (j : Nat) : Nat := getL oneK KI.CDIS (j - 1)
@[expose] noncomputable def DK : Nat := elK 21
@[expose] noncomputable def K1K : Nat := elK 22
@[expose] noncomputable def K2K : Nat := elK 23
@[expose] noncomputable def K1I : Nat := elIK 22
@[expose] noncomputable def K2I : Nat := elIK 23
@[expose] noncomputable def EK (i : Nat) : Nat := elK (24 + i)
@[expose] noncomputable def RK (i : Nat) : Nat := elK (27 + i)
@[expose] noncomputable def DM1 : Nat := Nat.xor DK oneK

@[expose] noncomputable def R0M (l : Nat) : Nat := getL 0 [AL, RK 0, RK 1, RK 2, RK 3, RK 4, RK 5] l

@[expose] noncomputable def inR0 (x : Nat) : Bool := bfsMemK R0T.P R0T.S R0T.N x

@[expose] noncomputable def commK (x y : Nat) : Bool := eqK (mulWK x y) (mulWK y x)

@[expose] noncomputable def cRN (i j : Nat) : Nat :=
  getL 0 [0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1,
    1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] (6 * i + j)

@[expose] noncomputable def prodE (n : Nat) : Nat :=
  mulWK (mulWK (mulWK (powWK DK (n % 3)) (powWK (EK 0) (n / 3 % 3))) (powWK (EK 1) (n / 9 % 3)))
    (powWK (EK 2) (n / 27 % 3))

theorem kDag : dagOK gBaseK (cWordsN.map CFSG.Sporadic.Co1Schreier.Native.decWord) KI.CDS KI.CDIS =
    true := by
  quickRfl

theorem kLen : Nat.beq KI.CDS.length 32 = true := by quickRfl

theorem kD : (eqK (powWK DK 3) oneK && notB (eqK DK oneK) && commK DK AL) = true := by quickRfl

theorem kInvS : andB (andB (canK DM1) (canK KI.DSI)) (Nat.beq (CFSG.KC.Co1B.mulK DM1 KI.DSI) oneK) =
    true := by
  quickRfl

theorem kRoots : (Nat.beq (vmF 24 (trK 24 (CertificateChecks.KernelCo1ThreeK.R.M 0)) 25668) 25668 &&
    Nat.beq (vmF 24 (trK 24 (CertificateChecks.KernelCo1ThreeK.R.M 1)) 452) 452 &&
    Nat.beq (vmF 24 (trK 24 (CertificateChecks.KernelCo1ThreeK.R.M 2)) 17819) 17819) = true := by
  quickRfl

theorem kR0 : (gtPinK R0M 7 128 R0T.N R0T.P R0T.PAR R0T.LAB R0T.W R0T.S && Nat.beq R0T.N 128) =
    true := by
  quickRfl

theorem kRi : allN 6 (fun i => andB (andB (commK (RK i) DK) (memQ (RK i)))
    (eqK (mulWK (RK i) (RK i)) oneK)) = true := by
  quickRfl

theorem kQ : impAllK (fun x => commK x DK) inR0 QL = true := by quickRfl

theorem kCR : allN 6 (fun i => allN 6 fun j => eqK (mulWK (RK i) (RK j))
    (mulWK (mulWK (RK j) (RK i)) (Bool.rec (motive := fun _ => Nat) oneK AL (Nat.beq (cRN i j) 1))))
    = true := by
  quickRfl

theorem kK : (commK K1K DK && commK K1K AL && commK K2K DK && commK K2K AL &&
    andB (andB (canK K1K) (canK K1I)) (Nat.beq (CFSG.KC.Co1B.mulK K1K K1I) oneK) &&
    andB (andB (canK K2K) (canK K2I)) (Nat.beq (CFSG.KC.Co1B.mulK K2K K2I) oneK)) = true := by
  quickRfl

theorem kRel : (CFSG.HardMathSupport.Dickson.I271.U42Presentation.u42Words.all fun w =>
    inR0 (relK K1K K2K K1I K2I w)) = true := by
  quickRfl

theorem kK1 : allN 128 (fun i => notB (eqK K1K (R0T.P i))) = true := by quickRfl

theorem kE : (allN 3 (fun i => andB (andB (eqK (powWK (EK i) 3) oneK) (commK (EK i) DK))
    (commK (EK i) AL)) && allN 3 (fun i => allN 3 fun j => commK (EK i) (EK j))) = true := by
  quickRfl

theorem kE81 : allN 81 (fun n => orB (Nat.beq n 0) (notB (eqK (prodE n) oneK))) = true := by
  quickRfl

theorem negD : notB (eqK (powWK DK 2) oneK) = true := by quickRfl

theorem negR0 : notB (gtPinK R0M 7 128 (R0T.N - 1) R0T.P R0T.PAR R0T.LAB R0T.W R0T.S) = true := by
  quickRfl

theorem negQ : notB (impAllK (fun x => commK x oneK) inR0 QL) = true := by quickRfl

theorem negK1 : notB (allN 128 fun i => notB (eqK (R0T.P 5) (R0T.P i))) = true := by quickRfl

theorem negE81 : notB (allN 81 fun n => notB (eqK (prodE n) oneK)) = true := by quickRfl

end CertificateChecks.KernelCo1I301

end
