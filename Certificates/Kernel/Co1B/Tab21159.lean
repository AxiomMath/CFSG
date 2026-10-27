module

public import Certificates.Data.Kernel.Co1BInner
public import Certificates.Kernel.Co1B.Data21159
public import Certificates.Kernel.Co1B.Tab21142
public import Certificates.Kernel.Co1B.Cnt21142
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def kwK (w : List Nat) : Nat :=
  w.foldl (fun acc j => mulK acc (getL oneK TWS (kIdx.getD j 0 - 1))) oneK

@[expose] noncomputable def kwiK (w : List Nat) : Nat :=
  w.foldl (fun acc j => mulK (getL oneK TWIS (kIdx.getD j 0 - 1)) acc) oneK

@[expose] noncomputable def V59 : List Nat := [oneK, AL42, W0L42, W0AL42]

theorem rx_chk : Nat.beq (ypT 34) RX59 = true := by quickRfl

theorem ry_chk : Nat.beq (mulWK (hpK 55) (ypT 108)) RY59 = true := by quickRfl

theorem g1_chk : Nat.beq (kwK [0, 1, 1, 1]) G159 = true := by quickRfl

theorem g2_chk : Nat.beq (kwK [1, 1, 1, 1, 1]) G259 = true := by quickRfl

theorem k1_chk : Nat.beq (getL oneK TWS 73) K159 = true := by quickRfl

@[expose] def cw59 (j : Nat) : List Nat := [[], [0], [1], [0, 0], [0, 1], [1, 0]].getD (j % 6) []

@[expose] noncomputable def ttChk (j : Nat) : Bool :=
  Nat.beq (mulK (mulK (kwK (cw59 j)) (Bool.rec (motive := fun _ => Nat) RY59 RX59 (Nat.blt j 6)))
    (kwiK (cw59 j))) (getL 0 T59 j)

#j4q_all CFSG.KD.Co1B.TT59 CertificateChecks.KernelCo1B.ttChk 12

@[expose] noncomputable def tsK (b S : Nat) : Nat :=
  (List.range 6).foldl (fun acc j => if S.testBit j = true then mulK acc (getL 0 T59 (b + j)) else acc) oneK

@[expose] noncomputable def tsChk (S : Nat) : Bool :=
  andB (Nat.beq (tsK 0 S) (getL 0 TS059 S)) (Nat.beq (tsK 6 S) (getL 0 TS659 S))

#j4q_all CFSG.KD.Co1B.TS59 CertificateChecks.KernelCo1B.tsChk 64

theorem ap_chk : decide (AP59 = YP42.flatMap fun Y => [Y, mulWK Y AL42]) = true := by quickRfl

@[expose] noncomputable def w1Chk (i : Nat) : Bool :=
  andB (andB (Nat.blt (getL 0 W1S59 i) 64) (Nat.blt (getL 0 W1V59 i) 4))
    (eqK (mulWK (getL 0 TS059 (getL 0 W1S59 i)) (getL 0 V59 (getL 0 W1V59 i))) (getL 0 AP59 i))

#j4q_all CFSG.KD.Co1B.W159 CertificateChecks.KernelCo1B.w1Chk 256

@[expose] noncomputable def w2Chk (i : Nat) : Bool :=
  andB (andB (Nat.blt (getL 0 W2S59 i) 64) (Nat.blt (getL 0 W2J59 i) 256))
    (eqK (mulWK (getL 0 TS659 (getL 0 W2S59 i)) (getL 0 AP59 (getL 0 W2J59 i)))
      (getL oneK TWS (hIdx.getD i 0 - 1)))

#j4q_all CFSG.KD.Co1B.W259 CertificateChecks.KernelCo1B.w2Chk 6

theorem comm_chk : (T59.all fun t => T59.all fun t' => V59.any fun v =>
    eqK (mulWK t t') (mulWK v (mulWK t' t))) = true := by quickRfl

end CertificateChecks.KernelCo1B

end
