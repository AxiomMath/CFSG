module

public import Certificates.Data.Kernel.L5.BaseMul
public import Certificates.Data.Kernel.L5.EngOne
public import Certificates.Data.Kernel.L5.Sh2FusT
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz_eval CFSG.KD.L5.Sh1R "Certificates/Data/Kernel/L5/data/sh1eng.json.gz" 6185
  5574037560382927535
  (C : Nat) (K : Nat) (I : Nat) (ciP : Nat) (cszP : Nat) (maxSubsP : List Nat) (reps : List Nat)
  (x : Nat) (mgens : List Nat) (ctx : List (List Nat)) (tags : List (List Nat))
  (paths : List (List Nat)) (embV : List Nat)

namespace CFSG.KD.L5.Sh1

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD.L5

@[expose] def ix (i : Nat) : Idx 128 := ⟨⟨i % 128, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def mul1 : Idx 128 → Idx 128 → Idx 128 := mulB 128 Sh1R.C Sh1R.K 7 0 6

@[expose] def inv1 : Idx 128 → Idx 128 := invB 128 Sh1R.I 7

@[expose] def one1 : Idx 128 := ix 0

@[expose] def unpack (P w : Nat) : List Nat := (List.range 128).map fun a => (P >>> (w * a)) % 2 ^ w

@[expose] def bitsA (m : Nat) : Array Bool := ((List.range 128).map fun a => m.testBit a).toArray

@[expose] def invs1 : List (Idx 128) :=
  ((List.range 128).filter fun u =>
    decide (mulBN 128 Sh1R.C Sh1R.K 7 0 6 u u = 0) && decide (u ≠ 0)).map ix

@[expose] def eng1R : Eng 128 where
  reps := Sh1R.reps.map ix
  members := []
  ciA := (unpack Sh1R.ciP 3).toArray
  cszA := (unpack Sh1R.cszP 9).toArray
  invs := invs1
  ctxs := []
  mgens := []
  wordA := #[]
  maxSubs := Sh1R.maxSubsP.map bitsA
  x := ix Sh1R.x

@[expose] def mgens1 : List (Idx 128) := Sh1R.mgens.map ix

@[expose] def ctx1 : List (List (Idx 128)) := Sh1R.ctx.map (List.map ix)

@[expose] def paths1 : List (List (Idx 128)) := Sh1R.paths.map (List.map ix)

@[expose] def ld1 : List Nat := [0, 0, 2, 0, 2, 2]

@[expose] noncomputable def eI1 (c : Nat) : Idx 128 :=
  ix (lookT ((Sh2FusT.embT.map Prod.fst).zip Sh1R.embV) c)

@[expose] noncomputable def embL1 (t : ↥T5) : Idx 128 := eI1 (codeP t.1)

end CFSG.KD.L5.Sh1

end
