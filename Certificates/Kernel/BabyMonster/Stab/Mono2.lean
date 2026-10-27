module

public import Certificates.Kernel.BabyMonster.Stab.Common
public import Certificates.Kernel.BabyMonster.Stab.Blk
public import CFSG.Certificates.Kernel.BabyMonster.StabCheck.Mono2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono13_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono13_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono13_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono13_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono19_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono19_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono19_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono19_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono21_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono21_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono21_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono21_3

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic CFSG.KC.BM.Ln

set_option maxRecDepth 100000

theorem stab13 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G13.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C13.rows i) i :=
  monoStab (Ms := M13.b0) (NM := nthN G13.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M13.b0 (nthN G13.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C13.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt13_ 274))
    net13 Stab.v13 Stab.al13
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne13_ 68) Stab.ne13t)

theorem stab19 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G19.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C19.rows i) i :=
  monoStab (Ms := M19.b0) (NM := nthN G19.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M19.b0 (nthN G19.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C19.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt19_ 274))
    net19 Stab.v19 Stab.al19
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne19_ 68) Stab.ne19t)

theorem stab21 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G21.b0 0))
    (recOf CFSG.KC.BM.FixedLine.C21.rows i) i :=
  monoStab (Ms := M21.b0) (NM := nthN G21.b0 1)
    (stOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M21.b0 (nthN G21.b0 1))
      (R := recOf CFSG.KC.BM.FixedLine.C21.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt21_ 274))
    net21 Stab.v21 Stab.al21
    (rowsNe_4371 (by forall_lt_consts CFSG.KC.BM.Dy.Stab.ne21_ 68) Stab.ne21t)

end CertificateChecks.KernelBM.Dy

end
