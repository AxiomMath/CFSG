module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Text
public import Certificates.Data.Kernel.Misc.RuInv

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Text

@[expose] noncomputable def powEqRK (n w m nw idn p e r : Nat) : Bool :=
  bAnd(canonK n w m nw p, Nat.beq (ppow n w m idn p e) r)

@[expose] noncomputable def rowKey (r : Nat × Nat × Nat × Nat) : Nat :=
  nIf(Nat.beq r.1 (nat_lit 1), r.2.2.1, r.2.2.2)

@[expose] noncomputable def readI (s : List (Nat × Nat)) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1000000) (fun q _ ih => nIf(Nat.beq q.1 k, q.2, ih)) s

@[expose] noncomputable def symAt (rows : List (Nat × Nat × Nat × Nat)) (t : Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → Nat → List (Nat × Nat) → List (Nat × Nat)) (fun _ _ s => s)
    (fun r _ ih c t s => Nat.rec (motive := fun _ => List (Nat × Nat)) s
      (fun t' _ => ih (Nat.succ c) t' (List.cons (rowKey r, Nat.add c (nat_lit 2)) s)) t)
    rows (nat_lit 0) t [(1, 0), (2, 1)]

@[expose] noncomputable def rowAt (rows : List (Nat × Nat × Nat × Nat)) (t : Nat) :
    Nat × Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat × Nat × Nat) (fun _ => (3, 0, 0, 0))
    (fun r _ ih t => Nat.rec (motive := fun _ => Nat × Nat × Nat × Nat) r (fun t' _ => ih t') t)
    rows t

@[expose] noncomputable def rowOK (rows : List (Nat × Nat × Nat × Nat)) (V : Nat → Nat) (t : Nat) :
    Bool :=
  strictB (Nat.add t (nat_lit 2)) (fun o => (fun s r =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (strictB (readI s r.2.2.1) (fun a => bAnd(Nat.blt a o,
            Nat.beq (CFSG.KC.Misc.RuInv.powP (V a) r.2.1) (V o))))
          (Nat.beq r.1 (nat_lit 2)))
        (strictB (readI s r.2.1) (fun a => bAnd(Nat.blt a o,
          permOK (nat_lit 4060) (nat_lit 12) (nat_lit 4095) (nat_lit 48720) (V a) (V o))))
        (Nat.beq r.1 (nat_lit 1)))
      (strictB (readI s r.2.1) (fun a => strictB (readI s r.2.2.1) (fun b =>
        bAnd(Nat.blt a o, bAnd(Nat.blt b o,
          Nat.beq (CFSG.KC.Misc.RuInv.mulP (V a) (V b)) (V o))))))
      (Nat.beq r.1 (nat_lit 0))) (symAt rows t) (rowAt rows t))

@[expose] noncomputable def finOK (rows : List (Nat × Nat × Nat × Nat)) (L : Nat) (V : Nat → Nat)
    (C D : Nat) : Bool :=
  (fun s => strictB (readI s 1) (fun a => strictB (readI s 2) (fun b =>
    bAnd(Nat.blt a (Nat.add L 2), bAnd(Nat.blt b (Nat.add L 2),
      bAnd(Nat.beq (V a) C, Nat.beq (V b) D)))))) (symAt rows L)

@[expose] noncomputable def takeK (k : Nat) (l : List Int) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun x _ ih k => Nat.rec (motive := fun _ => List Int) [] (fun k' _ => x :: ih k') k) l k

@[expose] noncomputable def dropK (k : Nat) (l : List Int) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun x xs ih k => Nat.rec (motive := fun _ => List Int) (x :: xs) (fun k' _ => ih k') k) l k

@[expose] noncomputable def wordAppK (n w m : Nat) (S SI : Nat → Nat) (kS : Nat) (wd : List Int)
    (P r : Nat) : Bool :=
  bAnd(szOK n w, bAnd(lettersK kS wd, Nat.beq (wordK n w m P S SI wd) r))

@[expose] noncomputable def lettersAllK (k : Nat) (ws : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun wd _ ih => bAnd(lettersK k wd, ih)) ws

@[expose] noncomputable def hexRun (wd bd cnt : Nat) (cs : List Char) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun e t _ => bAnd(Nat.beq e cnt, Nat.beq t (nat_lit 0)))
    (fun ch _ ih e t v => strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) wd,
          bIf(Nat.blt v' bd, ih (Nat.succ e) (nat_lit 0) (nat_lit 0), false),
          ih e (Nat.succ t) v')),
      false)))
    cs

@[expose] noncomputable def hexRunK (wd bd cnt : Nat) (cs : List Char) : Bool :=
  bAnd(Nat.blt (nat_lit 0) wd, hexRun wd bd cnt cs (nat_lit 0) (nat_lit 0) (nat_lit 0))

end CFSG.KS.SporSch

end
