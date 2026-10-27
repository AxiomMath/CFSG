module

public import Certificates.Data.Kernel.L5.BaseMul
public import Certificates.Data.Kernel.L5.EngOne
public import Certificates.Data.Kernel.L5.Sh2FusT
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.L5.E0 "Certificates/Data/Kernel/L5/data/eng0.json.gz" 12171
  2297653540975287356
  (codesP : Nat) (keyP : Nat) (invP : Nat) (embT : List (Nat × Nat)) (repsN : List Nat)
  (xN : Nat) (ciA : Array Nat) (cszA : Array Nat) (invsN : List Nat)
  (maxSubsA : List (Array Bool)) (mgensR : List Nat) (ctxR : List (List Nat))
  (pathsR : List (List Nat)) (tags : List (List Nat)) (r1P : Nat)

namespace CFSG.KD.L5.E0

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

@[expose] def ix (i : Nat) : Idx 128 := ⟨⟨i % 128, Nat.mod_lt _ (by decide)⟩⟩

@[expose] noncomputable def mul : Idx 128 → Idx 128 → Idx 128 := mulB 128 codesP keyP 7 0 6

@[expose] noncomputable def inv : Idx 128 → Idx 128 := invB 128 invP 7

@[expose] def one : Idx 128 := ix 0

@[expose] noncomputable def eng : Eng 128 where
  reps := repsN.map ix
  members := []
  ciA := ciA
  cszA := cszA
  invs := invsN.map ix
  ctxs := []
  mgens := []
  wordA := #[]
  maxSubs := maxSubsA
  x := ix xN

@[expose] noncomputable def mgens : List (Idx 128) := mgensR.map ix

@[expose] noncomputable def ctxs : List (List (Idx 128)) := ctxR.map (List.map ix)

@[expose] noncomputable def paths : List (List (Idx 128)) := pathsR.map (List.map ix)

@[expose] def ld0 : List Nat := [0, 1, 1, 0, 0, 1]

@[expose] def postB (r : Nat) (e : Eng 128) : Bool :=
  e.invs.all fun u => e.invs.all fun v =>
    !r.testBit u.v || !decide (blkOf e.ciA ld0 u = blkOf e.ciA ld0 v) || r.testBit v.v

@[expose] noncomputable def eI (c : Nat) : Idx 128 := ix (lookT embT c)

@[expose] noncomputable def embL (t : ↥T5) : Idx 128 := eI (codeP t.1)

end CFSG.KD.L5.E0

end
