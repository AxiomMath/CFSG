module

public import Certificates.Kernel.BabyMonster.Facts3102
public import Certificates.Kernel.BabyMonster.ForallSt
public import Certificates.Kernel.BabyMonster.Aligned
public import CFSG.Certificates.Kernel.BabyMonster.DyStab

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt

@[expose] noncomputable def failRow : Nat :=
  dyElim (nat_lit 256) CFSG.KC.BM.Dyadic.Bs (nat_lit 0) dyFail

theorem monoStab {Ms : List Nat} {T NM : Nat} {C : List (List Nat)}
    (hst : ∀ i < 4371, stOK CFSG.KC.BM.Dyadic.Bs (monoF CFSG.KC.BM.Dyadic.Bs Ms NM) (recOf C) i =
      true)
    (hn : netOK Ms T NM = true) (hv : netV Ms T = true) (hal : allAligned Ms = true)
    (hne : rowsNe C failRow 4371 = true) :
    ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumMono T) (recOf C i) i :=
  fun i hi => stMono_sound blocks rows Align.shifts hal hn hv hi (hst i hi)
    (rowsNe_sound hne i hi).1

theorem sparseStab {Cs SG C : List (List Nat)}
    (hst : ∀ i < 4371, stOK CFSG.KC.BM.Dyadic.Bs (colF CFSG.KC.BM.Dyadic.Bs Cs) (recOf C) i = true)
    (hal : allAlignedL Cs = true) (hd : selDisj Cs = true) (hcv : colV Cs = true)
    (hnc : Nat.beq (lenLL Cs) 16 = true) (hSG : blocksOK SG = true)
    (hc : ∀ m < 274, colorRowsL Cs dyDs (64 * (m / 4) + 16 * (m % 4))
      (takeN 16 (dropN (16 * (m % 4)) (CFSG.KC.YModel.lgetL SG (m / 4)))) = true)
    (hne : rowsNe C failRow 4371 = true) :
    ∀ i < 4371, RowStab CFSG.KC.BM.Dyadic.Bs (kNumSparse SG) (recOf C i) i :=
  fun i hi => stSparse_sound blocks rows Align.shifts hal hd hcv hnc hSG hc hi (hst i hi)
    (rowsNe_sound hne i hi).1 (rowsNe_sound hne i hi).2

end CertificateChecks.KernelBM.Dy

end
