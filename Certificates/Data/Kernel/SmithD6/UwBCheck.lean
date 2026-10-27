module

public import Certificates.Data.Kernel.SmithD6.UwCheck
public import Certificates.Data.Kernel.SmithD6.UwBData

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KC.Loop

@[expose] def ubTop : Nat := 9223372036854775808

@[expose] noncomputable def ubClsK (s : Nat) : Nat :=
  nIf(Nat.beq (fld(s, 0, 1)) 1, 3, nIf(KT.memB (Nat.xor ubTop s) wt64Tree, 1, 2))

@[expose] noncomputable def ubKOf (s : Nat) : Nat :=
  nIf(Nat.beq (fld(s, 63, 1)) 1, nIf(Nat.beq s ubTop, 0, ubClsK s), 0)

@[expose] noncomputable def ubRep (c : Nat) : Nat := JB.bReps.getD (Nat.pred c) 0

@[expose] noncomputable def ubParOK (d k f : Nat) : Bool :=
  bAnd(Nat.blt 0 f, bAnd(Nat.blt 0 (pkGet JB.bD 5 (Nat.pred f)),
    bAnd(Nat.blt (pkGet JB.bD 5 (Nat.pred f)) d, Nat.beq (pkGet JB.bK 2 (Nat.pred f)) k)))

@[expose] noncomputable def ubStepOK (v s d k : Nat) (r : Nat × Nat × Nat) : Bool :=
  bIf(Nat.beq d 1, Nat.beq v (ubRep k),
    bAnd(Nat.blt r.1 30, bAnd(Nat.beq (liftT (JU.uwT.getD (Nat.add 15 r.1) []) r.2.1) s,
      ubParOK d k (KT.find r.2.1 wt64Tree))))

@[expose] noncomputable def ubWitK (s k : Nat) : Bool :=
  bAnd(Nat.blt (Nat.div k 4096) (Nat.mod k 4096),
    bAnd(Nat.blt (Nat.mod k 4096) (Nat.xor (Nat.div k 4096) (Nat.mod k 4096)),
      bAnd(Nat.blt (Nat.xor (Nat.div k 4096) (Nat.mod k 4096)) 4096,
        bAnd(Nat.beq (Nat.land (Nat.div k 4096) 63) 0,
          bAnd(Nat.beq (Nat.land (Nat.mod k 4096) 63) 0,
            Nat.beq (Nat.xor ubTop (rhoK (Nat.div k 4096) (rhoK (Nat.mod k 4096) ubTop))) s)))))

@[expose] noncomputable def ubRecOK (v s : Nat) (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.beq (pkGet JB.bK 2 v) (ubKOf s),
    bIf(Nat.beq (pkGet JB.bK 2 v) 0, true,
      bAnd(Nat.ble (ubRep (pkGet JB.bK 2 v)) v,
        bAnd(Nat.blt 0 (pkGet JB.bD 5 v),
          bAnd(ubStepOK v s (pkGet JB.bD 5 v) (pkGet JB.bK 2 v) r,
            bIf(Nat.beq (pkGet JB.bK 2 v) 1, ubWitK s r.2.2, true))))))

@[expose] noncomputable def ubGo (ss : List Nat) : List (Nat × Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Nat → Bool) (fun rs _ => isNilB rs)
    (fun s _ ih rs v => List.rec (motive := fun _ => Bool) false
      (fun r rs' _ => bAnd(ubRecOK v s r, strictKB (Nat.succ v) (ih rs'))) rs) ss

@[expose] noncomputable def ubNth (cs : List (List (Nat × Nat × Nat))) :
    Nat → List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat × Nat)) (fun _ => [])
    (fun ch _ ih c => Nat.rec (motive := fun _ => List (Nat × Nat × Nat)) ch (fun c' _ => ih c') c)
    cs

@[expose] noncomputable def ubOK (c : Nat) : Bool :=
  ubGo (nthC J.wt64C c) (ubNth JB.bRC c) (Nat.mul 2048 c)

@[expose] noncomputable def ubKeysGo (l : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(bIf(Nat.beq r.2.2 0, true, lineTree.memB r.2.2), ih)) l

@[expose] noncomputable def ubKeysOK : Bool :=
  List.rec (motive := fun _ => Bool) true (fun ch _ ih => bAnd(ubKeysGo ch, ih)) JB.bRC

@[expose] noncomputable def ubHeadK : Bool :=
  Nat.beq (KT.find ubTop wt64Tree) (Nat.succ JB.bE0) &&
    (List.range 30).all (fun g => liftT (JU.uwT.getD (15 + g) []) ubTop == ubTop) &&
    JB.bReps.length == 3 &&
    [1, 2, 3].all fun c => decide (ubRep c < 75735) && pkGet JB.bK 2 (ubRep c) == c

@[expose] noncomputable def ubCnt (c : Nat) : Nat :=
  sumBelow 75735 1184 fun j => nIf(Nat.beq (pkGet JB.bK 2 j) c, 1, 0)

end CFSG.KD.SmithD6

end
