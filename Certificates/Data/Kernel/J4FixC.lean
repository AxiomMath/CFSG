module

public import Certificates.Data.Kernel.SporSch.J4SCols
public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.J4Count

public section

namespace CFSG.KC.J4FixC

open CFSG.KC.Enum CFSG.KS.SporSch.C11 CFSG.KC.J4Count
open CFSG.KC.J4Q (vecJ)

@[expose] noncomputable def notK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def nth {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l i

@[expose] def codeL : Nat → Int
  | 0 => 1
  | 1 => -1
  | 2 => 2
  | _ => -2

@[expose] def toI (w : List Nat) : List Int := w.map codeL

@[expose] def invI (w : List Nat) : List Int := (toI w).reverse.map Neg.neg

@[expose] def invW (w : List Nat) : List Nat := w.reverse.map fun c => c + 1 - 2 * (c % 2)

@[expose] noncomputable def mkP (a C : Nat) : Nat := Nat.add a (Nat.mul C (nat_lit 2048))

@[expose] noncomputable def paK (p : Nat) : Nat := Nat.mod p (nat_lit 2048)

@[expose] noncomputable def pcK (p : Nat) : Nat := Nat.div p (nat_lit 2048)

@[expose] noncomputable def pmulK (p q : Nat) : Nat :=
  strictN p fun p => strictN q fun q =>
    mkP (Nat.xor (paK p) (appK (pcK p) (paK q))) (compK (pcK p) (pcK q))

@[expose] noncomputable def pidP : Nat := mkP (nat_lit 0) pidK

@[expose] noncomputable def peqK (p q : Nat) : Bool :=
  bAnd(Nat.beq (paK p) (paK q), allN (nat_lit 11) fun j => Nat.beq (colK (pcK p) j) (colK (pcK q) j))

@[expose] noncomputable def genP (X XI Y YI : Nat) (g : List Nat × Nat) : Nat :=
  strictN (wordColsK X XI Y YI (toI g.1)) fun C => mkP (appK C g.2) C

@[expose] noncomputable def genIP (X XI Y YI : Nat) (g : List Nat × Nat) : Nat :=
  mkP g.2 (wordColsK X XI Y YI (invI g.1))

@[expose] noncomputable def letP (GP GIP : List Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0), nth pidP GP (Nat.div c (nat_lit 2)),
    nth pidP GIP (Nat.div c (nat_lit 2)))

@[expose] noncomputable def evalW (GP GIP : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pidP (fun c _ ih => pmulK (letP GP GIP c) ih) w

@[expose] noncomputable def letM (MX MXI MY MYI c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), MX, nIf(Nat.beq c (nat_lit 1), MXI, nIf(Nat.beq c (nat_lit 2), MY, MYI)))

@[expose] noncomputable def walkK (rm MX MXI MY MYI : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun c _ ih v => strictN (vecJ rm v (letM MX MXI MY MYI c)) ih) w

@[expose] noncomputable def fixAllK (rm MX MXI MY MYI : Nat) (eta : Nat → Nat → Nat) (v : Nat)
    (G : List (List Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(Nat.blt g.2 (nat_lit 2048),
      bAnd(Nat.beq (eta (walkK rm MX MXI MY MYI g.1 v) g.2) v, ih))) G

@[expose] noncomputable def distinctK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p t ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(notK (peqK p q), ih')) t, ih)) L

@[expose] noncomputable def memPK (p : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun q _ ih => bIf(peqK p q, true, ih)) L

@[expose] noncomputable def closedK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih' => bAnd(memPK (pmulK p q) L, ih')) L, ih)) L

@[expose] noncomputable def tagK (RL : List Nat) (p f t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (notK (Nat.beq (fixCntK (pcK p)) (nat_lit 32)))
    (fun r _ => peqK (pmulK f p) (pmulK (nth pidP RL r) f)) t

@[expose] noncomputable def commK (r : Nat) (CL : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(peqK (pmulK c r) (pmulK r c), ih)) CL

@[expose] noncomputable def sortedK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih prev => strictB (pcK p) fun k => bAnd(canonK k, bAnd(Nat.blt prev k, ih k))) L

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  foldN n (fun a s => nIf(f a, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def cntAK (B P : List Nat) (C : Nat) : Nat :=
  cntN (nat_lit 2048) fun a => bAnd(Nat.beq (combo B (decode P a)) a, Nat.beq (appK C a) a)

end CFSG.KC.J4FixC

end
