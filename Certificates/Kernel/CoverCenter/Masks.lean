module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_list_root CFSG.KD.CoverMasks.J3 "Certificates/Kernel/CoverCenter/data/J3.masks.items" 2000 9129 13246894747714498939
#kc_repo #kc_list_root CFSG.KD.CoverMasks.McL "Certificates/Kernel/CoverCenter/data/McL.masks.items" 2000 265834 16943348805670009780

namespace CFSG.KD.CoverMasks

@[expose] noncomputable def mcl : List Nat :=
  [McL.c0, McL.c1, McL.c2, McL.c3, McL.c4, McL.c5, McL.c6, McL.c7, McL.c8, McL.c9, McL.c10,
    McL.c11, McL.c12, McL.c13, McL.c14, McL.c15, McL.c16, McL.c17, McL.c18, McL.c19, McL.c20,
    McL.c21, McL.c22, McL.c23, McL.c24, McL.c25, McL.c26, McL.c27, McL.c28, McL.c29].flatten

end CFSG.KD.CoverMasks

end
