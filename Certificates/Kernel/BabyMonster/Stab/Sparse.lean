module

public import Certificates.Kernel.BabyMonster.Stab.Common
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse24_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse24_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse24_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse24_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse25_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse25_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse25_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Sparse25_3
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Check4

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic CFSG.KC.BM.Ln

set_option maxRecDepth 100000

theorem stab24 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumSparse SG24)
    (recOf CFSG.KC.BM.FixedLine.C24.rows i) i :=
  sparseStab (Cs := Align.colors24)
    (stOK_of_lanes lnData (F := colF CFSG.KC.BM.Dyadic.Bs Align.colors24)
      (R := recOf CFSG.KC.BM.FixedLine.C24.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt24_ 274))
    Align.colors24_aligned Align.colors24_disj (by quickRfl) ncols24 (by quickRfl)
    (by forall_lt_cols CFSG.KC.BM.Dyadic.cols24_ 274) (by quickRfl)

theorem stab25 : ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumSparse SG25)
    (recOf CFSG.KC.BM.FixedLine.C25.rows i) i :=
  sparseStab (Cs := Align.colors25)
    (stOK_of_lanes lnData (F := colF CFSG.KC.BM.Dyadic.Bs Align.colors25)
      (R := recOf CFSG.KC.BM.FixedLine.C25.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt25_ 274))
    Align.colors25_aligned Align.colors25_disj (by quickRfl) ncols25 (by quickRfl)
    (by forall_lt_cols CFSG.KC.BM.Dyadic.cols25_ 274) (by quickRfl)

end CertificateChecks.KernelBM.Dy

end
