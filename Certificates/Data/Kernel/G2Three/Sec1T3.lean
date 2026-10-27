module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def M128 : Nat := Nat.sub (Nat.shiftLeft 1 128) 1

@[expose] noncomputable def M896 : Nat := Nat.sub (Nat.shiftLeft 1 896) 1

@[expose] noncomputable def hasB (m i : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i))

@[expose] noncomputable def rowT (P x : Nat) : Nat := fld(P, Nat.mul 896 x, M896)

@[expose] noncomputable def atR (r j : Nat) : Nat := fld(r, Nat.mul 7 j, 127)

@[expose] noncomputable def imgR (r H : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => nIf(hasB H i, Nat.lor acc (Nat.shiftLeft 1 (atR r i)), acc)) 128

@[expose] noncomputable def conjR (rx cv g : Nat) : Nat := atR cv (atR rx g)

@[expose] noncomputable def commE (P C V x y : Nat) : Nat :=
  atR (rowT C (atR V y)) (conjR (rowT P x) (rowT C (atR V x)) y)

@[expose] noncomputable def pairAt (lo t : Nat) : Nat := fld(lo, Nat.add 16 (Nat.mul 16 t), 65535)

@[expose] noncomputable def ordAt (OR k : Nat) : Nat := fld(OR, Nat.mul 8 k, 255)

@[expose] noncomputable def pairsOK (P C Q L OR h H lo : Nat) : Bool :=
  (fun d => Nat.rec (motive := fun _ => Bool) true (fun t ih => bAnd(
    (fun p => (fun k x => (fun K => bIf(Nat.blt t d,
        bAnd(Bool.not' (hasB H x), bAnd(hasB H (atR Q x), bAnd(
          Nat.beq K (Nat.lor H (imgR (rowT C x) H)), Nat.beq K (Nat.lor H (imgR (rowT P x) H))))),
        bAnd(Nat.beq (Nat.land H K) H, Nat.beq (ordAt OR k) (Nat.mul 2 (ordAt OR h)))))
      (fld(L, Nat.mul 128 k, M128))) (Nat.land p 511) (Nat.shiftRight p 9)) (pairAt lo t), ih))
    (Nat.land lo 255)) (fld(lo, 8, 255))

@[expose] noncomputable def unionU (L lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t acc =>
    Nat.lor acc (fld(L, Nat.mul 128 (Nat.land (pairAt lo t) 511), M128))) (Nat.land lo 255)

@[expose] noncomputable def idxU (lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t acc =>
    Nat.lor acc (Nat.shiftLeft 1 (Nat.land (pairAt lo t) 511))) (fld(lo, 8, 255))

@[expose] noncomputable def witB (rx cv H gs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun t ih =>
    bIf(Bool.not' (hasB H (conjR rx cv (fld(gs, Nat.add 3 (Nat.mul 7 t), 127)))), true, ih))
    (Nat.land gs 7)

@[expose] noncomputable def gensIn (H gs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih =>
    bAnd(hasB H (fld(gs, Nat.add 3 (Nat.mul 7 t), 127)), ih)) (Nat.land gs 7)

@[expose] noncomputable def coverOK (P C V Q G H U gs : Nat) : Bool :=
  allBelow 128 2 fun x =>
    bIf(hasB G x, bIf(hasB H x, true, bIf(hasB U x, true,
      bIf(hasB H (atR Q x), witB (rowT P x) (rowT C (atR V x)) H gs, true))), true)

@[expose] noncomputable def rowOK (P C V Q G L LG OR h lo : Nat) : Bool :=
  (fun H gs => bAnd(Nat.beq (Nat.land H G) H, bAnd(gensIn H gs, bAnd(pairsOK P C Q L OR h H lo,
      coverOK P C V Q G H (unionU L lo) gs))))
    (fld(L, Nat.mul 128 h, M128)) (fld(LG, Nat.mul 64 h, Nat.sub (Nat.shiftLeft 1 64) 1))

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def rowsOK (P C V Q G L LG OR : Nat) (LO : List Nat) (h : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun lo _ ih h => bAnd(rowOK P C V Q G L LG OR h lo, strictB (Nat.succ h) ih)) LO h

@[expose] noncomputable def idxAll (LO : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun lo _ acc => Nat.lor (idxU lo) acc) LO

@[expose] noncomputable def cenK (P C G gs : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(bAnd(hasB G i, (fun r =>
      Nat.rec (motive := fun _ => Bool) true (fun t ih => (fun g =>
        bAnd(Nat.beq (atR r g) (atR (rowT C i) g), ih)) (fld(gs, Nat.mul 7 t, 127))) 5)
      (rowT P i)),
    Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128

@[expose] noncomputable def z2K (P C V G Z gs : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(bAnd(hasB G i, (fun rx cv =>
      Nat.rec (motive := fun _ => Bool) true (fun t ih => (fun g =>
        bAnd(hasB Z (atR (rowT C (atR V g)) (conjR rx cv g)), ih)) (fld(gs, Nat.mul 7 t, 127))) 5)
      (rowT P i) (rowT C (atR V i))),
    Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128

@[expose] noncomputable def pop (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(hasB m i, Nat.succ acc, acc)) 128

@[expose] noncomputable def ordK (L OR lo m : Nat) : Bool :=
  allBelow m 7 fun j => (fun k => Nat.beq (pop (fld(L, Nat.mul 128 k, M128))) (ordAt OR k))
    (Nat.add lo j)

@[expose] noncomputable def rtA (RT x s : Nat) : Nat :=
  fld(RT, Nat.mul 7 (Nat.add (Nat.mul 6 x) s), 127)

@[expose] noncomputable def tabK (P RT PA PB lo m : Nat) : Bool :=
  allBelow m 2 fun l => (fun i => (fun r => bAnd(Nat.beq (atR r 0) i,
      Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(Nat.beq (atR r (Nat.succ j))
        (rtA RT (atR r (fld(PA, Nat.mul 7 j, 127))) (fld(PB, Nat.mul 7 j, 127))), ih)) 127))
    (rowT P i)) (Nat.add lo l)

@[expose] noncomputable def colK (P C lo m : Nat) : Bool :=
  allBelow m 2 fun l => (fun i => (fun r =>
      Nat.rec (motive := fun _ => Bool) true (fun j ih =>
        bAnd(Nat.beq (atR (rowT C j) i) (atR r j), ih)) 128)
    (rowT P i)) (Nat.add lo l)

@[expose] noncomputable def invK (P V : Nat) : Bool :=
  allBelow 128 2 fun i => Nat.beq (atR (rowT P i) (atR V i)) 0

@[expose] noncomputable def sqK (P Q : Nat) : Bool :=
  allBelow 128 2 fun i => Nat.beq (atR Q i) (atR (rowT P i) i)

end CFSG.KD.G2Three.Sec1T3
