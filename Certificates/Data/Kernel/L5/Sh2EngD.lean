module

public import Certificates.Data.Kernel.L5.EngWit
public import Certificates.Data.Kernel.L5.Sh2Mul
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz_eval CFSG.KD.L5 "Certificates/Data/Kernel/L5/data/sh2eng.json.gz" 4179
  7801186606563420261 (cszP : Nat) (maxSubsP : List Nat) (ciPA : Nat) (ciPB : Nat)
  (tagsA : List (List Nat)) (tagsB : List (List Nat))

#kc_repo #kc_json_gz_eval CFSG.KD.L5.Sh2EngR "Certificates/Data/Kernel/L5/data/sh2eng.json.gz"
  4179 7801186606563420261 (repsA : List Nat) (repsB : List Nat) (xA : Nat) (xB : Nat)
  (mgensR : List Nat) (ctxA : List (List Nat)) (ctxB : List (List Nat))

namespace CFSG.KD.L5

open CFSG.GH74.GLS.C3.Layer2.L5.Fus

@[expose] def ix (i : Nat) : Idx 256 := ⟨⟨i % 256, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def unpackN (P w : Nat) : List Nat := (List.range 256).map fun a => (P >>> (w * a)) % 2 ^ w

@[expose] def bitsA (m : Nat) : Array Bool := ((List.range 256).map fun a => m.testBit a).toArray

@[expose] def invsN (ty : Nat) : List (Idx 256) :=
  ((List.range 256).filter fun u => decide (mulN ty u u % 256 = 0) && decide (u ≠ 0)).map ix

@[expose] def engD (ty : Nat) (reps : List Nat) (x ciP cszP : Nat) (ms : List Nat) : Eng 256 where
  reps := reps.map ix
  members := []
  ciA := (unpackN ciP 3).toArray
  cszA := (unpackN cszP 9).toArray
  invs := invsN ty
  ctxs := []
  mgens := []
  wordA := #[]
  maxSubs := ms.map bitsA
  x := ix x

@[expose] def engA (ty : Nat) : Eng 256 := engD ty Sh2EngR.repsA Sh2EngR.xA ciPA cszP maxSubsP

@[expose] def engB (ty : Nat) : Eng 256 := engD ty Sh2EngR.repsB Sh2EngR.xB ciPB cszP maxSubsP

@[expose] def mgensR : List (Idx 256) := Sh2EngR.mgensR.map ix

@[expose] def ctxA : List (List (Idx 256)) := Sh2EngR.ctxA.map (List.map ix)

@[expose] def ctxB : List (List (Idx 256)) := Sh2EngR.ctxB.map (List.map ix)

end CFSG.KD.L5

end
