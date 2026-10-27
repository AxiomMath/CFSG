module

public import Certificates.Kernel.D4QK.Elts
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.D4QK.TreeB
public import Certificates.Kernel.D4QK.Trees

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.D4QK
open CFSG.KC.Co1B (mulWK)
open CFSG.Quasithin.Background.Harris.R1.D4Vert (qR1 qR2 qR12)

@[expose] noncomputable def ordK : Bool :=
  bAnd(eqM (mulWK Y1 Y1I) oneK, bAnd(eqM (mulWK Y2 Y2) oneK, bAnd(eqM (powK ZE 7) oneK,
    notB (eqM (mulWK Y1 Y1) oneK))))

theorem ord : ordK = true := by quickRfl

theorem rel1 : relsK (phK ZP Y1 oneK) (phK ZP Y1I oneK) qR1 = true := by quickRfl

theorem rel2 : relsK (phK ZP oneK Y2) (phK ZP oneK Y2) qR2 = true := by quickRfl

theorem rel12 : relsK (phK ZP Y1 Y2) (phK ZP Y1I Y2) qR12 = true := by quickRfl

theorem invQ : invTK QT.P 2048 = true := by quickRfl

theorem pairs : pairCheckK ZP qR1 qR2 qR12 QT.P 2048 KT.P 42 Y1 Y2 = true := by quickRfl

theorem commKc : commK ZE KT.P 42 = true := by quickRfl

theorem cubeKc : cubeK S0 S0I KT.P 42 = true := by quickRfl

end CertificateChecks.KernelD4Q

end
