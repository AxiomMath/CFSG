module

public import Certificates.Kernel.D4QK.Elts
public import Certificates.Kernel.S63K.IData
public import Certificates.Data.Kernel.S63K.ConjTree
public import Certificates.Data.Kernel.SporSch.Co1Mat
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.D4QK.TreeB
public import Certificates.Kernel.D4QK.Trees

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.D4QK
open CFSG.KC.Co1B (mulWK)
open CFSG.Quasithin.Background.Harris.R1.D4Vert (nWords tabQ2 tabKc)
open CertificateChecks.KernelS63

@[expose] noncomputable def eltsK : Bool :=
  bAnd(eqM Y1 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 0 [])),
  bAnd(eqM Y2 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 1 [])),
  bAnd(eqM ZE (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 2 [])),
  bAnd(eqM R0 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 3 [])),
  bAnd(eqM S0 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 4 [])),
  bAnd(Nat.beq oneK CFSG.KS.SporSch.M24.idM,
  bAnd(Nat.beq (GK 0) ZE, bAnd(Nat.beq (GK 1) R0, bAnd(Nat.beq (GK 2) S0, Nat.beq (GZ 0) ZE)))))))))

theorem elts : eltsK = true := by quickRfl

@[expose] noncomputable def zpowK : Bool :=
  bAnd(allN 7 fun i => eqM (ZP i) (powK ZE i), eqM (powK ZE 7) oneK)

theorem zpow : zpowK = true := by quickRfl

theorem gq : (allN 14 fun l => eqM (GQ l) (phK ZP Y1 Y2 l)) = true := by quickRfl

theorem gqi : (allN 14 fun l => eqM (mulWK (GQ l) (phK ZP Y1I Y2 l)) oneK) = true := by quickRfl

@[expose] noncomputable def invsK : Bool :=
  bAnd(eqM (mulWK ZE (ZP 6)) oneK, bAnd(eqM (mulWK R0 R0) oneK, bAnd(eqM (mulWK S0 S0I) oneK,
    bAnd(eqM (mulWK Y1 Y1I) oneK, eqM (mulWK Y2 Y2) oneK))))

theorem invs : invsK = true := by quickRfl

theorem gs : (allN 14 fun l => eqM (GS l) (phK ZP C1 C2 l)) = true := by quickRfl

theorem gsi : (allN 14 fun l => eqM (mulWK (GS l) (phK ZP C1I C2I l)) oneK) = true := by quickRfl

theorem plQ : plK QT.PAR QT.LAB QT.N tabQ2 1 = true := by quickRfl

theorem plKc : plK KT.PAR KT.LAB KT.N tabKc 1 = true := by quickRfl

end CertificateChecks.KernelD4Q

end
