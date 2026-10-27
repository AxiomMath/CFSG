module

public import Certificates.Kernel.Co1OddB.Data
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.Co1B.Data2046
public import Certificates.Data.Kernel.Co1OddB
public import Certificates.Data.Kernel.Co1FixList

public section

namespace CertificateChecks.KernelCo1OddB

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.F2W CFSG.KC.Co1OddB CFSG.KC.Co1Fix CFSG.KC.M1F2
  CFSG.Sporadic.Co1Schreier

theorem prog_ok : progK 24 RB Data.oddBProg 3 = true := by decide +kernel

theorem take3 : RB.take 3 = [CertificateChecks.KernelCo1Cover.R0, CertificateChecks.KernelCo1Cover.R1,
    CFSG.KD.Co1B.SBK] := by decide +kernel

theorem len : RB.length = 25 ∧ HP.length = 24 ∧ VX.length = 8 ∧ VY.length = 8 ∧
    Data.oddHWords.length = 24 ∧ Data.oddPerfX.length = 8 ∧ Data.oddPerfY.length = 8 := by
  decide +kernel

theorem comm_fix : ([9, 14, 19, 24].all fun i =>
    eqK (mulW 24 (RB.getD i 0) CFSG.KD.Co1B.SBK)
      (mulW 24 CFSG.KD.Co1B.SBK (RB.getD i 0)) &&
    vmF 24 (trK 24 (RB.getD i 0)) 10075731 == 10075731) = true := by decide +kernel

theorem orders : (eqK (powWK (RB.getD 9 0) 3) oneK && eqK (powWK (RB.getD 19 0) 3) oneK &&
    eqK (powWK (RB.getD 14 0) 5) oneK && eqK (powWK (RB.getD 24 0) 5) oneK &&
    !eqK (powWK (mulW 24 (RB.getD 9 0) (RB.getD 19 0)) 15) oneK &&
    !eqK (powWK (mulW 24 (RB.getD 14 0) (RB.getD 24 0)) 15) oneK) = true := by decide +kernel

theorem words : ((Data.oddHWords.zip HP).all fun p => progK 24 [RB.getD 9 0, RB.getD 14 0, p.2] [p.1] 2)
    = true ∧ ((Data.oddPerfX.zip VX).all fun p => progK 24 [RB.getD 9 0, RB.getD 14 0, p.2] [p.1] 2)
    = true ∧ ((Data.oddPerfY.zip VY).all fun p => progK 24 [RB.getD 9 0, RB.getD 14 0, p.2] [p.1] 2)
    = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem perf : (eqK (VX.foldl (mulW 24) oneK) (RB.getD 9 0) &&
    eqK (VY.foldl (mulW 24) oneK) (RB.getD 14 0) &&
    [(0, 2), (1, 3), (4, 6), (5, 7)].all (fun p => eqK (mulW 24 (VX.getD p.1 0) (VX.getD p.2 0)) oneK &&
      eqK (mulW 24 (VY.getD p.1 0) (VY.getD p.2 0)) oneK)) = true := by decide +kernel

theorem basis : (vmF 24 (trK 24 (RB.getD 14 0)) 6217977 == 6217977 &&
    vmF 24 (trK 24 (RB.getD 14 0)) 14517350 == 14517350 &&
    Nat.beq (usK HP 6217977 14517350) BT && Nat.beq (mulF 24 BT BTI) (idF 24) &&
    eqK (mulW 24 BTI BT) oneK) = true := by decide +kernel

theorem fixed : Nat.beq (trK 24 (RB.getD 14 0)) YT = true ∧ fixK 24 YT 0 FY YY 8 256 0 = true ∧
    fixListK YT YT FY W = true ∧ W.length = 256 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] noncomputable def candRow (k : Nat) : Bool :=
  ((W.drop (8 * k)).take 8).all fun u0 => W.all fun u1 =>
    candM (trK 24 (RB.getD 9 0)) (trK 24 (RB.getD 14 0)) (trK 24 CFSG.KD.Co1B.SBK) BT BTI
      (usK HP u0 u1)

end CertificateChecks.KernelCo1OddB

end
