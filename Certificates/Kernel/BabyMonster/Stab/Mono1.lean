module

public import Certificates.Kernel.BabyMonster.Stab.Common
public import Certificates.Kernel.BabyMonster.Stab.Blk
public import CFSG.Certificates.Kernel.BabyMonster.StabCheck.Mono1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono6_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono6_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono6_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono6_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono7_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono7_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono7_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono7_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono8_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono8_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono8_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono8_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono9_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono9_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono9_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono9_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono10_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono10_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono10_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono10_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono12_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono12_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono12_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono12_3

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic CFSG.KC.BM.Ln

set_option maxRecDepth 100000

theorem stab6 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G6.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C6.rows i) i :=
  monoStab (Ms := M6.b0) (NM := nthN G6.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M6.b0 (nthN G6.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C6.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt6_ 274))
    net6 Stab.v6 Stab.al6
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne6_ 68) Stab.ne6t)

theorem stab7 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G7.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C7.rows i) i :=
  monoStab (Ms := M7.b0) (NM := nthN G7.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M7.b0 (nthN G7.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C7.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt7_ 274))
    net7 Stab.v7 Stab.al7
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne7_ 68) Stab.ne7t)

theorem stab8 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G8.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C8.rows i) i :=
  monoStab (Ms := M8.b0) (NM := nthN G8.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M8.b0 (nthN G8.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C8.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt8_ 274))
    net8 Stab.v8 Stab.al8
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne8_ 68) Stab.ne8t)

theorem stab9 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G9.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C9.rows i) i :=
  monoStab (Ms := M9.b0) (NM := nthN G9.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M9.b0 (nthN G9.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C9.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt9_ 274))
    net9 Stab.v9 Stab.al9
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne9_ 68) Stab.ne9t)

theorem stab10 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G10.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C10.rows i) i :=
  monoStab (Ms := M10.b0) (NM := nthN G10.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M10.b0 (nthN G10.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C10.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt10_ 274))
    net10 Stab.v10 Stab.al10
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne10_ 68) Stab.ne10t)

theorem stab12 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G12.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C12.rows i) i :=
  monoStab (Ms := M12.b0) (NM := nthN G12.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M12.b0 (nthN G12.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C12.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt12_ 274))
    net12 Stab.v12 Stab.al12
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne12_ 68) Stab.ne12t)

end CertificateChecks.KernelBM.Dy

end
