module

public import CFSG.Certificates.Kernel.DAKSound
public import Certificates.Kernel.DAK.C510
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.DAK510

open Certificates.DAK

#kc_forall_tree da510all (fun i => dakSingleAt 5 10 F S i = true) 16 CFSG.KD.DAK510.da510

theorem cells : CFSG.StandardType.GGDepASmallCells 5 10 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine CFSG.StandardType.DAK.dak_cells (by decide) (by decide) (by decide) F S da510frame
    da510cover (fun i hi => da510all i ?_)
  rwa [da510len] at hi

end CFSG.KD.DAK510

end
