module

public import Certificates.Data.Kernel.D4PlaneP
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlaneData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.D4Plane "Certificates/Kernel/D4Plane/data/d4plane.json.gz" 14146
  4444949420986295314 (ls : List Nat) (es : List Nat) (om : List Nat) (ps : List (List Nat))

namespace CFSG.KD.D4Plane

open CFSG.KC.D4PlaneP CFSG.AGLEmbedding.D4Two

theorem lettersOK : (List.range 18).all (fun i => packA (letterArr i) == ls.getD i 0) = true := by
  decide +kernel

theorem enumOK : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true := by decide +kernel

theorem omOK : (es.filter cube1P == om) = true := by decide +kernel

theorem psOK : (d4PlaneCerts.map (fun c => c.idxs.map (atP es)) == ps) = true := by decide +kernel

theorem coverOK : coverR om ps = true := by decide +kernel

theorem planesOK : d4PlaneCerts.all (fun c => poolP ls es c && targetP ls c) = true := by
  decide +kernel

theorem enumNeg : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar (es.set 1 0) = false := by
  decide +kernel

theorem coverNeg : coverR om (ps.drop 1) = false := by decide +kernel

theorem planesNeg :
    (d4PlaneCerts.take 1).all (fun c => poolP ls es c && targetP (ls.set 3 0) c) = false := by
  decide +kernel

end CFSG.KD.D4Plane

end
