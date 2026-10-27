module

public import Certificates.Kernel.D4QK.Elts
public import Certificates.Kernel.S63K.IData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Data.Kernel.S63K.ConjTree
public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.D4HexLinkCheck
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.D4QK.TreeB
public import Certificates.Kernel.D4QK.Trees

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.D4QK
open CFSG.KC.Co1B (mulWK)
open CFSG.Quasithin.Background.Harris.R1.D4Vert (nWords hWords)
open CertificateChecks.KernelS63

@[expose] noncomputable def X0 : Nat := wordK ID.G CFSG.KS.SporSch.M24.idM (hWords.getD 1 [])

@[expose] noncomputable def Z0 : Nat := ID.ZP 0

@[expose] noncomputable def flagK : Bool :=
  bAnd(CFSG.D4Hex.sortKey (HD.ptW (nWords.getD 4 []) 0) (HD.ptW (nWords.getD 4 []) 1)
      (HD.ptW (nWords.getD 4 []) 5) == CFSG.D4Hex.lineKey 0 1 5,
  bAnd(notB (Nat.beq (HD.ptW (nWords.getD 4 []) 0) 0),
  bAnd(Nat.beq (HD.ptW (hWords.getD 2 []) 0) 0, Nat.beq (HD.ptW (hWords.getD 3 []) 0) 0)))

theorem flag : flagK = true := by quickRfl

theorem x0vb : eqM X0 (ID.ZP 1) = true := by quickRfl

@[expose] noncomputable def zconjK : Bool :=
  bAnd(eqM (mulWK ZE (ID.G 0)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [2]) ZE),
  bAnd(eqM (mulWK ZE (ID.G 1)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [0, 1]) ZE),
  bAnd(eqM (mulWK ZE (ID.G 2)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [1, 2]) ZE),
    eqM (mulWK ZE (ID.G 6)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [0, 2, 6, 0, 2]) ZE))))

theorem zconj : zconjK = true := by quickRfl

theorem vcomm : (allN 14 fun l => strictB (GQ l) fun g =>
    bAnd(eqM (mulWK g Z0) (mulWK Z0 g), eqM (mulWK g X0) (mulWK X0 g))) = true := by quickRfl

theorem r0nc : notB (eqM (mulWK R0 X0) (mulWK X0 R0)) = true := by quickRfl

theorem center : centerK GQ 14 Z0 X0 (mulWK Z0 X0) QT.P 2048 = true := by quickRfl

theorem kc : kcK GQ 14 KT.P 42 = true := by quickRfl

theorem sin : (allN 14 fun l => strictB (GS l) fun Y => anyK 2048 fun w => eqM (QT.P w) Y) = true := by
  quickRfl

end CertificateChecks.KernelD4Q

end
