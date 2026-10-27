module

public import Certificates.Data.SmithD6Uw
public import Certificates.Data.Kernel.SmithD6.UwData
public import Certificates.Data.Kernel.SmithD6.WtCheck
public import Certificates.Data.Kernel.SmithD6.Trees
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KC.Loop

@[expose] noncomputable def uwClsK (s : Nat) : Nat :=
  nIf(Nat.beq s 1, 0, nIf(KT.memB (Nat.xor 1 s) wt64Tree, 1,
    nIf(Nat.beq (fld(s, 63, 1)) 1, 3, 2)))

@[expose] noncomputable def uwRep (c : Nat) : Nat := JU.uwReps.getD c 0

@[expose] noncomputable def uwParOK (d k f : Nat) : Bool :=
  bAnd(Nat.blt 0 f, bAnd(Nat.blt 0 (pkGet JU.uwD 5 (Nat.pred f)),
    bAnd(Nat.blt (pkGet JU.uwD 5 (Nat.pred f)) d, Nat.beq (pkGet JU.uwK 2 (Nat.pred f)) k)))

@[expose] noncomputable def uwStepOK (v s d : Nat) (r : Nat × Nat) : Bool :=
  bIf(Nat.beq d 1, Nat.beq v (uwRep (pkGet JU.uwK 2 v)),
    bAnd(Nat.blt r.1 45, bAnd(Nat.beq (liftT (JU.uwT.getD r.1 []) r.2) s,
      uwParOK d (pkGet JU.uwK 2 v) (KT.find r.2 wt64Tree))))

@[expose] noncomputable def uwRecOK (v s : Nat) (r : Nat × Nat) : Bool :=
  bAnd(Nat.beq (pkGet JU.uwK 2 v) (uwClsK s),
    bAnd(Nat.ble (uwRep (pkGet JU.uwK 2 v)) v,
      bAnd(Nat.blt 0 (pkGet JU.uwD 5 v), uwStepOK v s (pkGet JU.uwD 5 v) r)))

@[expose] noncomputable def uwOrbGo (ss : List Nat) : List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Bool) (fun rs _ => isNilB rs)
    (fun s _ ih rs v => List.rec (motive := fun _ => Bool) false
      (fun r rs' _ => bAnd(uwRecOK v s r, strictKB (Nat.succ v) (ih rs'))) rs) ss

@[expose] noncomputable def nthR (cs : List (List (Nat × Nat))) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun ch _ ih c => Nat.rec (motive := fun _ => List (Nat × Nat)) ch (fun c' _ => ih c') c) cs

@[expose] noncomputable def uwOrbOK (c : Nat) : Bool :=
  uwOrbGo (nthC J.wt64C c) (nthR JU.uwRC c) (Nat.mul 2048 c)

@[expose] def uwGL : List (Nat × Nat) :=
  ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
    if a < b then some (fV a, fV b) else none) ++
  ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
    if a != b then some (eV a, fV b) else none)

@[expose] noncomputable def uwGenK (g : Nat) : Bool :=
  lineTree.memB (4096 * (uwGL.getD g (0, 0)).1 + (uwGL.getD g (0, 0)).2) &&
    decide ((uwGL.getD g (0, 0)).1 < (uwGL.getD g (0, 0)).2) &&
    decide ((uwGL.getD g (0, 0)).2 < ((uwGL.getD g (0, 0)).1 ^^^ (uwGL.getD g (0, 0)).2)) &&
    decide ((uwGL.getD g (0, 0)).1 ^^^ (uwGL.getD g (0, 0)).2 < 4096) &&
    rhoTOK (uwGL.getD g (0, 0)).1 (uwGL.getD g (0, 0)).2 (JU.uwT.getD g []) &&
    liftT (JU.uwT.getD g []) 1 == 1

@[expose] noncomputable def uwHeadK : Bool :=
  uwGL.length == 45 && (List.range 45).all uwGenK && JU.uwReps.length == 4 &&
    (List.range 4).all fun c => decide (uwRep c < 75735) && pkGet JU.uwK 2 (uwRep c) == c

@[expose] noncomputable def uwCnt (c : Nat) : Nat :=
  sumBelow 75735 1184 fun j => nIf(Nat.beq (pkGet JU.uwK 2 j) c, 1, 0)

end CFSG.KD.SmithD6

end
