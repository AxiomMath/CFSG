module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KD.J2H2

open CFSG.KC.Enum

@[expose] noncomputable def getL {α : Type} (d : α) (L : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih i => Nat.rec (motive := fun _ => α) a (fun j _ => ih j) i) L i

@[expose] noncomputable def rowsPack (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor r (Nat.shiftLeft ih 49152)) L

@[expose] noncomputable def rowAt (HP x : Nat) : Nat :=
  fld(HP, Nat.mul 49152 x, Nat.sub (Nat.shiftLeft 1 49152) 1)

@[expose] noncomputable def fieldAt (V h : Nat) : Nat :=
  fld(V, Nat.mul 384 h, Nat.sub (Nat.shiftLeft 1 384) 1)

@[expose] noncomputable def repN : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.lor 1 (Nat.shiftLeft ih 384)) 128

@[expose] noncomputable def hvR (R j t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun r ih => Nat.lor ih (Nat.shiftLeft fld(R, Nat.add (Nat.mul 384 t) (Nat.add (Nat.mul 32 r) j), 1) r))
    12

@[expose] noncomputable def hv (HP j x t : Nat) : Nat := hvR (rowAt HP x) j t

@[expose] noncomputable def mulRowK (sp : List Nat) (R LN : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun s _ ih c => Nat.xor (Nat.mul s (Nat.land (Nat.shiftRight R (Nat.mul 32 c)) LN)) (ih (Nat.succ c)))
    sp 0

@[expose] noncomputable def rowX (sp : List Nat) (R L Q b REP : Nat) : Nat :=
  Nat.xor (Nat.xor (mulRowK sp R (Nat.mul REP 1073741823)) L) (Nat.mul (fieldAt Q b) REP)

@[expose] noncomputable def rowFin (MTP Q X b : Nat) : Bool :=
  allN 128 (fun h => Nat.beq (fieldAt X h) (fieldAt Q (pg 7 127 MTP (Nat.add (Nat.mul 128 b) h))))

@[expose] noncomputable def rowQ (HP REP LMP MTP : Nat) (sp : List Nat) (k b Q : Nat) : Bool :=
  rowFin MTP Q (rowX sp (rowAt HP b) (rowAt HP (pg 7 127 LMP (Nat.add (Nat.mul 128 k) b))) Q b REP) b

@[expose] noncomputable def rowOK (HP REP LMP MTP : Nat) (SP : List (List Nat)) (k b : Nat) : Bool :=
  rowQ HP REP LMP MTP (getL [] SP k) k b (rowAt HP (Nat.succ k))

@[expose] noncomputable def rowOKf (HP REP LMP MTP : Nat) (SP : List (List Nat)) (i : Nat) : Bool :=
  rowOK HP REP LMP MTP SP (Nat.div i 128) (Nat.mod i 128)

@[expose] noncomputable def normK (HP : Nat) : Bool :=
  bAnd(Nat.beq (rowAt HP 0) 0, allN 128 (fun x => Nat.beq (fieldAt (rowAt HP x) 0) 0))

@[expose] noncomputable def treeK (HP GP PP : Nat) : Bool :=
  allN 127 (fun x => Nat.beq
    (fieldAt (rowAt HP (Nat.succ (pg 2 3 GP (Nat.succ x)))) (pg 7 127 PP (Nat.succ x))) 0)

@[expose] noncomputable def bitF (HP j f : Nat) : Nat :=
  fld(rowAt HP (Nat.succ (Nat.div f 1536)),
    Nat.add (Nat.mul 384 (Nat.mod (Nat.div f 12) 128)) (Nat.add (Nat.mul 32 (Nat.mod f 12)) j), 1)

@[expose] noncomputable def freeK (HP : Nat) (F : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 30)
    (fun f _ ih i => bAnd(Nat.blt f 4608,
      bAnd(allN 30 (fun j => Nat.beq (bitF HP j f) (nIf(Nat.beq i j, 1, 0))), ih (Nat.succ i)))) F 0

@[expose] noncomputable def listK (w m T : Nat) (L : List Nat) (o n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun a _ ih i => bAnd(Nat.beq (pg w m T i) a, ih (Nat.succ i))) L o

@[expose] noncomputable def lmK (LMP : Nat) (lL : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k 3)
    (fun row _ ih k => bAnd(listK 7 127 LMP row (Nat.mul 128 k) (Nat.add (Nat.mul 128 k) 128),
      ih (Nat.succ k))) lL 0

@[expose] noncomputable def dataK (GP PP LMP : Nat) (genL parL : List Nat) (lL : List (List Nat)) :
    Bool :=
  bAnd(listK 2 3 GP genL 0 128, bAnd(listK 7 127 PP parL 0 128, lmK LMP lL))

@[expose] noncomputable def mtK (MTP LMP GP PP : Nat) : Bool :=
  allN 128 (fun x => allN 128 (fun h => Nat.beq (pg 7 127 MTP (Nat.add (Nat.mul 128 x) h))
    (nIf(Nat.beq x 0, h, pg 7 127 LMP (Nat.add (Nat.mul 128 (pg 2 3 GP x))
      (pg 7 127 MTP (Nat.add (Nat.mul 128 (pg 7 127 PP x)) h)))))))

@[expose] noncomputable def mulColsK (P : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun col _ ih c => Nat.xor (Nat.mul fld(x, c, 1) col) (ih (Nat.succ c))) P 0

@[expose] noncomputable def matMulK (P Q : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun q _ ih => mulColsK P q :: ih) Q

@[expose] noncomputable def id12 : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

@[expose] noncomputable def matWordK (A B : List Nat) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun j _ ih acc => ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) B A (Nat.beq j 0)))) w id12

@[expose] noncomputable def spread (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun r ih => Nat.lor ih (Nat.shiftLeft fld(v, r, 1) (Nat.mul 32 r))) 12

@[expose] noncomputable def spRowK (sp cols : List Nat) : Bool :=
  allN 12 (fun c => Nat.beq (getL 0 sp c) (spread (getL 0 cols c)))

@[expose] noncomputable def spyK (SP : List (List Nat)) (A B : List Nat) (yW : List (List Nat)) : Bool :=
  allN 3 (fun k => spRowK (getL [] SP k) (matWordK A B (getL [] yW k)))

end CFSG.KD.J2H2

end
