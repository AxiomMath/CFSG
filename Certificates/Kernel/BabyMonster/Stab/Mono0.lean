module

public import Certificates.Kernel.BabyMonster.Stab.Common
public import Certificates.Kernel.BabyMonster.Stab.Blk
public import CFSG.Certificates.Kernel.BabyMonster.StabCheck.Mono0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono0_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono0_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono0_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono0_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono1_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono1_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono1_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono1_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono2_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono2_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono2_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono2_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono3_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono3_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono3_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono3_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono4_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono4_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono4_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono4_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono5_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono5_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono5_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono5_3

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic CFSG.KC.BM.Ln

set_option maxRecDepth 100000

theorem stab0 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G0.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C0.rows i) i :=
  monoStab (Ms := M0.b0) (NM := nthN G0.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M0.b0 (nthN G0.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C0.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt0_ 274))
    net0 Stab.v0 Stab.al0
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne0_ 68) Stab.ne0t)

theorem stab1 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G1.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C1.rows i) i :=
  monoStab (Ms := M1.b0) (NM := nthN G1.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M1.b0 (nthN G1.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C1.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt1_ 274))
    net1 Stab.v1 Stab.al1
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne1_ 68) Stab.ne1t)

theorem stab2 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G2.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C2.rows i) i :=
  monoStab (Ms := M2.b0) (NM := nthN G2.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M2.b0 (nthN G2.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C2.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt2_ 274))
    net2 Stab.v2 Stab.al2
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne2_ 68) Stab.ne2t)

theorem stab3 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G3.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C3.rows i) i :=
  monoStab (Ms := M3.b0) (NM := nthN G3.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M3.b0 (nthN G3.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C3.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt3_ 274))
    net3 Stab.v3 Stab.al3
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne3_ 68) Stab.ne3t)

theorem stab4 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G4.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C4.rows i) i :=
  monoStab (Ms := M4.b0) (NM := nthN G4.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M4.b0 (nthN G4.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C4.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt4_ 274))
    net4 Stab.v4 Stab.al4
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne4_ 68) Stab.ne4t)

theorem stab5 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G5.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C5.rows i) i :=
  monoStab (Ms := M5.b0) (NM := nthN G5.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M5.b0 (nthN G5.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C5.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt5_ 274))
    net5 Stab.v5 Stab.al5
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne5_ 68) Stab.ne5t)

end CertificateChecks.KernelBM.Dy

end
