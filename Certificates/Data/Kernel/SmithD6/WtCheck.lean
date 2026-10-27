module

public import Certificates.Data.Kernel.SmithD6.Clifford
public import Certificates.Data.Kernel.SmithD6.Terms
public import Certificates.Data.Kernel.SmithD6.Tree64
public import Certificates.Data.Kernel.KeyTreeChunks

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] def gensV : List (Nat × Nat) :=
  [(1, 2), (1, 128), (64, 2), (2, 256), (128, 4), (4, 512), (256, 8), (8, 1024), (512, 16),
    (16, 2048), (1024, 32), (16, 32), (1024, 2048)]

@[expose] def evL : List Nat :=
  [0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30, 33, 34, 36, 39, 40, 43, 45, 46, 48,
    51, 53, 54, 57, 58, 60, 63]

@[expose] noncomputable def isNilB {α : Type} (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def exGo (s : Nat) (es : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun e _ ih k => Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight s k) 1) e) (ih (Nat.succ k)))
    es

@[expose] noncomputable def exC (s : Nat) : Nat := exGo s evL 0

@[expose] noncomputable def exPinGo (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun b => isNilB b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y r _ => bAnd(Nat.blt x 4294967296, bAnd(Nat.beq (exC x) y, ih r))) b) a

@[expose] noncomputable def d6ExOK (c : Nat) : Bool := exPinGo (nthC J.wtC c) (nthC J.wt64C c)

@[expose] noncomputable def closeGo (t : KT) (ts : List (Nat × Nat × Bool)) (l : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(KT.memB (liftT ts s) t, ih)) l

@[expose] noncomputable def d6CloseOK (c g : Nat) : Bool :=
  closeGo wt64Tree (JT.gensT.getD g []) (nthC J.wt64C c)

@[expose] noncomputable def colGo (p : Nat) (bs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih k => Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b p) 1) k) (ih (Nat.succ k)))
    bs

@[expose] noncomputable def pivGo (bs : List Nat) (ps : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih m => bAnd(Nat.beq (colGo p bs 0) (Nat.shiftLeft 1 m), ih (Nat.succ m))) ps

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def wK (s m sh x i : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (Nat.land s m) sh) (fld(x, i, 1))

@[expose] noncomputable def cK (s m sh x i : Nat) : Nat :=
  Nat.mul (Nat.shiftRight (Nat.land s m) sh) (fld(x, i, 1))

@[expose] noncomputable def rhoK (x s : Nat) : Nat :=
  Nat.xor
    (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0
      (wK s 0x5555555555555555 1 x 0)) (wK s 0x3333333333333333 2 x 1))
      (wK s 0x0F0F0F0F0F0F0F0F 4 x 2)) (wK s 0x00FF00FF00FF00FF 8 x 3))
      (wK s 0x0000FFFF0000FFFF 16 x 4)) (wK s 0x00000000FFFFFFFF 32 x 5))
    (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0
      (cK s 0xAAAAAAAAAAAAAAAA 1 x 6)) (cK s 0xCCCCCCCCCCCCCCCC 2 x 7))
      (cK s 0xF0F0F0F0F0F0F0F0 4 x 8)) (cK s 0xFF00FF00FF00FF00 8 x 9))
      (cK s 0xFFFF0000FFFF0000 16 x 10)) (cK s 0xFFFFFFFF00000000 32 x 11))

@[expose] noncomputable def annGo (s : Nat) (bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.blt b 4096, bAnd(Nat.beq (rhoK b s) 0, ih))) bs

@[expose] noncomputable def planeL (s : Nat) (bs ps : List Nat) : Bool :=
  bAnd(Nat.blt 0 s, bAnd(Nat.beq (lenN bs) 6, bAnd(Nat.beq (lenN ps) 6,
    bAnd(annGo s bs, pivGo bs ps 0))))

@[expose] noncomputable def planeA (s : Nat) (B P : Array Nat) : Bool :=
  Array.rec (motive := fun _ => Bool)
    (fun bs => Array.rec (motive := fun _ => Bool) (fun ps => planeL s bs ps) P) B

@[expose] noncomputable def planeGo (ss : List Nat) :
    List (Array Nat) → List (Array Nat) → Bool :=
  List.rec (motive := fun _ => List (Array Nat) → List (Array Nat) → Bool)
    (fun Bs Ps => bAnd(isNilB Bs, isNilB Ps))
    (fun s _ ih Bs Ps =>
      List.rec (motive := fun _ => Bool) false
        (fun B Bs' _ => List.rec (motive := fun _ => Bool) false
          (fun P Ps' _ => bAnd(planeA s B P, ih Bs' Ps')) Ps) Bs) ss

@[expose] noncomputable def nthA (cs : List (List (Array Nat))) : Nat → List (Array Nat) :=
  List.rec (motive := fun _ => Nat → List (Array Nat)) (fun _ => [])
    (fun ch _ ih c => Nat.rec (motive := fun _ => List (Array Nat)) ch (fun c' _ => ih c') c) cs

@[expose] noncomputable def d6PlaneOK (c : Nat) : Bool :=
  planeGo (nthC J.wt64C c) (nthA J.pbC c) (nthA J.ppC c)

end CFSG.KD.SmithD6

end
