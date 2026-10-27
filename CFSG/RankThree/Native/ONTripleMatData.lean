module

public import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.RankThree.Native.ONTriple
  "CFSG/RankThree/Native/data/ONTripleMat.json.gz" 840887 2657957031868258234
  (genC : List Nat) (genIC : List Nat) (regC : List Nat) (regIC : List Nat) (ptsC : List Nat)
  (pivF : List Nat) (blkRegs : List Nat) (blkF : List Nat) (autC : List Nat) (autIC : List Nat)

public section

namespace CFSG.RankThree.Native.ONTriple

@[expose] def chunksF : Nat → Nat → List Nat → List (List Nat)
  | 0, _, _ => []
  | k + 1, n, l => l.take n :: chunksF k n (l.drop n)

@[expose] noncomputable def pivM : List (List Nat) := chunksF 60 8 pivF

@[expose] noncomputable def blkPerms : List (List Nat) := chunksF 24 60 blkF

end CFSG.RankThree.Native.ONTriple

end
