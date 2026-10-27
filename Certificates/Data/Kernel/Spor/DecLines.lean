module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.DecLines

@[expose] noncomputable def encodeL (E : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun l _ ih => List.rec (motive := fun _ => List Nat) (List.cons (nat_lit 0) ih)
      (fun x _ ih2 => List.cons (Nat.succ x) ih2) l) E

@[expose] noncomputable def emit (t : Nat) (T : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h rest _ => bAnd(Nat.beq h t, k rest)) T

@[expose] noncomputable def emitIf (b : Bool) (t : Nat) (T : List Nat) (k : List Nat → Bool) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) (k T) (emit t T k) b

@[expose] noncomputable def run (cs : List Char) : Bool → Nat → Bool → Bool → List Nat → Bool :=
  List.rec (motive := fun _ => Bool → Nat → Bool → Bool → List Nat → Bool)
    (fun hd cur num ne T => Bool.rec (motive := fun _ => Bool)
      (emitIf num (Nat.succ cur) T fun T => emitIf ne (nat_lit 0) T fun T =>
        List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T)
      false hd)
    (fun ch _ ih hd cur num ne T =>
      (fun c => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              false
              (ih false (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub c (nat_lit 48))) true true T)
              (bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57))))
            (emitIf num (Nat.succ cur) T fun T => ih false (nat_lit 0) false true T)
            (Nat.beq c (nat_lit 32)))
          (emitIf num (Nat.succ cur) T fun T => emitIf ne (nat_lit 0) T fun T =>
            ih false (nat_lit 0) false false T)
          (Nat.beq c (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool) (ih true (nat_lit 0) false true T)
          (Bool.rec (motive := fun _ => Bool) false (ih false (nat_lit 0) false false T) ne)
          (Nat.beq c (nat_lit 10)))
        hd) (Char.toNat ch))
    cs

@[expose] noncomputable def linesChk (cs : List Char) (T : List Nat) : Bool :=
  run cs true (nat_lit 0) false false T

end CFSG.KS.DecLines

end
