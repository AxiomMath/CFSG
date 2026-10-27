module

public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs
import CFSG.Sporadic.Recognition.LyonsFinalDist2
import Certificates.Kernel.LyReplay.Facts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal in
theorem certificate6115 : ∀ r ∈ dist2Relators, FreeGroup.mk r ∈ Subgroup.normalClosure
    {x : FreeGroup (Fin 6) |
      x ∈ ((kkRel :: trRel dist2TrEv :: dist2EEvs.map eRelOf) ++ dist2BWords).map FreeGroup.mk} :=
  mk_dist2_mem_normalClosure
    (fun w hw => List.mem_map_of_mem (List.mem_append_right _ hw))
    (List.mem_map_of_mem (by simp))
    (fun e he => List.mem_map_of_mem (by simp [List.mem_map_of_mem he]))
    (List.mem_map_of_mem (by simp))
    KernelLyReplay.dist2Replays_true

end Certificates
