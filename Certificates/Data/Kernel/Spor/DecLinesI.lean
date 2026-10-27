module

public import Certificates.Data.Kernel.Spor.DecLines

public section

namespace CFSG.KS.DecLines

@[expose] noncomputable def tokI (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => Nat.succ (Nat.mul (nat_lit 2) n))
    (fun n => Nat.succ (Nat.succ (Nat.mul (nat_lit 2) n))) z

@[expose] noncomputable def encodeLI (E : List (List Int)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun l _ ih => List.rec (motive := fun _ => List Nat) (List.cons (nat_lit 0) ih)
      (fun x _ ih2 => List.cons (tokI x) ih2) l) E

@[expose] noncomputable def wordI (cur : Nat) (neg : Bool) (T : List Nat) (k : List Nat → Bool) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) (emit (Nat.succ (Nat.mul (nat_lit 2) cur)) T k)
    (bAnd(Nat.blt (nat_lit 0) cur, emit (Nat.mul (nat_lit 2) cur) T k)) neg

@[expose] noncomputable def endI (num neg : Bool) (cur : Nat) (T : List Nat) (k : List Nat → Bool) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (k T) false neg)
    (wordI cur neg T k) num

@[expose] noncomputable def runI (cs : List Char) : Bool → Nat → Bool → Bool → Bool → List Nat → Bool :=
  List.rec (motive := fun _ => Bool → Nat → Bool → Bool → Bool → List Nat → Bool)
    (fun hd cur num neg ne T => Bool.rec (motive := fun _ => Bool)
      (endI num neg cur T fun T => emitIf ne (nat_lit 0) T fun T =>
        List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T)
      false hd)
    (fun ch _ ih hd cur num neg ne T =>
      (fun c => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool)
                false
                (ih false (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub c (nat_lit 48))) true neg true T)
                (bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57))))
              (Bool.rec (motive := fun _ => Bool) false (ih false (nat_lit 0) false true true T)
                (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false neg)
                  false num))
              (Nat.beq c (nat_lit 45)))
            (endI num neg cur T fun T => ih false (nat_lit 0) false false true T)
            (Nat.beq c (nat_lit 32)))
          (endI num neg cur T fun T => emitIf ne (nat_lit 0) T fun T =>
            ih false (nat_lit 0) false false false T)
          (Nat.beq c (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool) (ih true (nat_lit 0) false false true T)
          (Bool.rec (motive := fun _ => Bool) false (ih false (nat_lit 0) false false false T) ne)
          (Nat.beq c (nat_lit 10)))
        hd) (Char.toNat ch))
    cs

@[expose] noncomputable def linesChkI (cs : List Char) (T : List Nat) : Bool :=
  runI cs true (nat_lit 0) false false false T

end CFSG.KS.DecLines

end
