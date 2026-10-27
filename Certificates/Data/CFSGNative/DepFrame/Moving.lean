module

public import Certificates.Data.CFSGNative.DepFrame.Check

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.NineAll

set_option compiler.extract_closed false

@[expose] def buildM (P0 : Pt) : Option NTables :=
  let roots := rootsOf P0 20000
  let rootsR := roots.map (·.r)
  let cand := candList P0 rootsR
  let ot1 := orbitTable P0 P0.gens.length 20000 (movingOf P0 cand)
  let reps? := ot1.1.mapM fun t => classifyD P0 cand t
  reps?.map fun reps => ⟨roots, [], [], ot1.2, reps⟩

@[expose] def verifyRepM (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  match rp.kind with
  | .w (.weyl _) => false
  | _ => verifyRepD P0 cand rp

@[expose] def verifyAllM (P0 : Pt) (T : NTables) : Bool :=
  wfCheck P0 && vFixN P0 && vRootsN P0 T &&
  (let cand := candOfN P0 T
   vCover1 P0 T cand && T.orb1.all (entry1OK P0 T) && T.reps.all (verifyRepM P0 cand) &&
   T.orb1.all (centEntryOK P0 T))

@[expose] def checkFrameM (P0 : Pt) : Bool :=
  match buildM P0 with
  | some T => verifyAllM P0 T
  | none => false

end CFSG.DepFrame

end
