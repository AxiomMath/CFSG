module

public import CFSG.Certificates.Kernel.DAKSound
public import Certificates.Kernel.DAK.C77
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.DAK77

open Certificates.DAK

#kc_forall_tree da77all (fun i => dakSingleAt 7 7 F S i = true) 18 CFSG.KD.DAK77.da77

theorem cells : CFSG.StandardType.GGDepASmallCells 7 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine CFSG.StandardType.DAK.dak_cells (by decide) (by decide) (by decide) F S da77frame
    da77cover (fun i hi => da77all i ?_)
  rwa [da77len] at hi

end CFSG.KD.DAK77

end
