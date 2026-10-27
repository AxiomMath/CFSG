module

public import Certificates.Kernel.Co1M.D10067
public import Certificates.Data.Kernel.Co1M.InvFam
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree

theorem k67_l0 : chunksK (actV RTS67 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) 13 12545053
    (recT l0L67 6 40) 275 24 3 9 64 0 5 = true := by quickRfl

theorem k67_l1 : chunksK (actV RTS67 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) 11 14887792
    (recT l1L67 6 38) 112 24 3 7 64 0 2 = true := by quickRfl

theorem k67_l2 : chunksK (actV RTS67 [4, 5, 6, 7, 8, 9, 10, 11, 12]) 9 7268220
    (recT l2L67 6 36) 30 24 3 5 64 0 1 = true := by quickRfl

theorem k67_l3 : chunksK (actV RTS67 [6, 7, 8, 9, 10, 11, 12]) 7 12571739
    (recT l3L67 6 29) 2 24 1 1 64 0 1 = true := by quickRfl

theorem k67_l4 : chunksK (actV RTS67 [6, 7, 9, 10, 11, 12]) 6 4035488
    (recT l4L67 6 34) 27 24 2 5 64 0 1 = true := by quickRfl

theorem k67_l5 : chunksK (actV RTS67 [9, 10, 11, 12]) 4 3503328
    (recT l5L67 6 29) 3 24 1 2 64 0 1 = true := by quickRfl

theorem k67_l6 : chunksK (actV RTS67 [11, 12]) 2 16500514
    (recT l6L67 6 27) 2 24 1 1 64 0 1 = true := by quickRfl

theorem k67_l7 : chunksK (actV RTS67 [11]) 1 14979871
    (recT l7L67 6 29) 3 24 2 2 64 0 1 = true := by quickRfl

@[expose] noncomputable def tyF67 (q : Nat) : Bool :=
  chunksK (actV RTA67 [13, 18, 23]) 3 359217 (recT tyL67 6 46) 47104 24 4 16 64 (Nat.mul q 100) 100

end CertificateChecks.KernelCo1M

#kc_slices CertificateChecks.KernelCo1M.TYx67 CertificateChecks.KernelCo1M.tyF67 8

end
