module

public import Certificates.Data.Kernel.J4Q.QT2A
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.J4Loc

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def fld (w P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def lenK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def rowL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def blkL (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List (List Nat)) m (fun j _ => ih j) i) l i

@[expose] noncomputable def actK (r : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih c => Nat.xor
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) x (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1)))
      (ih (Nat.shiftRight c (nat_lit 1)))) r

@[expose] noncomputable def mapK (r : List Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (actK r x) ih) l

@[expose] noncomputable def keyK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) x)) l

@[expose] noncomputable def subK (a b : Nat) : Bool := Nat.beq (Nat.land a b) a

@[expose] noncomputable def xorL (v : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (Nat.xor x v) ih) l

@[expose] noncomputable def appK (l l' : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) l' (fun x _ ih => List.cons x ih) l

@[expose] noncomputable def spanK (b : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons (nat_lit 0) List.nil)
    (fun v _ ih => appK ih (xorL v ih)) b

@[expose] noncomputable def nodupFrom (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => andB (notB (bitB acc x)) (ih (Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)))) l

@[expose] noncomputable def nodupK (l : List Nat) : Bool := nodupFrom l (nat_lit 0)

@[expose] noncomputable def octL (c : Nat) : List Nat :=
  [nat_lit 0, fld (nat_lit 11) c (nat_lit 0), fld (nat_lit 11) c (nat_lit 1), fld (nat_lit 11) c (nat_lit 2),
    fld (nat_lit 11) c (nat_lit 3), fld (nat_lit 11) c (nat_lit 4), fld (nat_lit 11) c (nat_lit 5),
    fld (nat_lit 11) c (nat_lit 6)]

@[expose] noncomputable def sortedC (c : Nat) : Bool :=
  andB (Nat.blt c (Nat.shiftLeft (nat_lit 1) (nat_lit 77)))
    (andB (Nat.blt (nat_lit 0) (fld (nat_lit 11) c (nat_lit 0)))
      (allR (nat_lit 6) fun k => Nat.blt (fld (nat_lit 11) c k) (fld (nat_lit 11) c (Nat.succ k))))

@[expose] noncomputable def treeOK (TR N I0 i r : Nat) : Bool :=
  strictB (fld (nat_lit 8) r (nat_lit 11)) fun d =>
    Bool.rec (motive := fun _ => Bool)
      (strictB (fld (nat_lit 12) r (nat_lit 6)) fun p =>
        strictB (fld (nat_lit 4) r (nat_lit 21)) fun l =>
          andB (Nat.blt p N) (andB (Nat.blt l (nat_lit 6))
            (strictB (fld (nat_lit 96) TR p) fun rp =>
              andB (Nat.beq (fld (nat_lit 12) rp l) i)
                (Nat.beq (Nat.succ (fld (nat_lit 8) rp (nat_lit 11))) d))))
      (Nat.beq i I0) (Nat.beq d (nat_lit 0))

@[expose] noncomputable def octOK (LR : List (List Nat)) (TK TR N I0 i : Nat) : Bool :=
  strictB (fld (nat_lit 80) TK i) fun c =>
    strictB (keyK (octL c)) fun K =>
      strictB (fld (nat_lit 96) TR i) fun r =>
        andB (sortedC c)
          (andB (orB (notB (Nat.blt (Nat.succ i) N)) (Nat.blt c (fld (nat_lit 80) TK (Nat.succ i))))
            (andB (allL (octL c) fun a => allL (octL c) fun b => bitB K (Nat.xor a b))
              (andB (allR (nat_lit 6) fun l =>
                  strictB (fld (nat_lit 12) r l) fun j =>
                    andB (Nat.blt j N)
                      (Nat.beq (keyK (mapK (rowL LR l) (octL c))) (keyK (octL (fld (nat_lit 80) TK j)))))
                (treeOK TR N I0 i r))))

@[expose] noncomputable def octBlk (LR : List (List Nat)) (TK TR N I0 k : Nat) : Bool :=
  allR (nat_lit 32) fun j =>
    orB (notB (Nat.blt (Nat.add (Nat.mul (nat_lit 32) k) j) N))
      (octOK LR TK TR N I0 (Nat.add (Nat.mul (nat_lit 32) k) j))

@[expose] noncomputable def subOK (SB : List (List Nat)) (SBK : List Nat) (KT KIT : List (List Nat))
    (b : Nat) : Bool :=
  strictB (getN (nat_lit 0) SBK b) fun K =>
    andB (Nat.beq K (keyK (spanK (rowL SB b))))
      (andB (nodupK (spanK (rowL SB b)))
        (allL (rowL SB b) fun v => allR (nat_lit 4) fun i =>
          andB (bitB K (actK (rowL KT i) v)) (bitB K (actK (rowL KIT i) v))))

@[expose] noncomputable def chainOK (SB : List (List Nat)) (SBK : List Nat) (KT : List (List Nat))
    (m b : Nat) : Bool :=
  strictB (getN (nat_lit 0) SBK b) fun K =>
    strictB (lenK (rowL SB b)) fun n =>
      CFSG.KC.Enum.allN (nat_lit 2048) fun v =>
        orB (bitB K v)
          (orB (notB (allR (nat_lit 4) fun i => bitB K (Nat.xor (actK (rowL KT i) v) v)))
            (anyK m fun T =>
              andB (subK K (getN (nat_lit 0) SBK T))
                (andB (bitB (getN (nat_lit 0) SBK T) v) (Nat.beq (lenK (rowL SB T)) (Nat.succ n)))))

@[expose] noncomputable def tabK (TLB : List (List (List Nat))) (e : Nat) : List Nat :=
  rowL (blkL TLB (Nat.div e (nat_lit 32))) (Nat.mod e (nat_lit 32))

@[expose] noncomputable def invK (t : List Nat) : Bool :=
  allR (nat_lit 11) fun j => Nat.beq (actK t (getN (nat_lit 0) t j)) (Nat.shiftLeft (nat_lit 1) j)

@[expose] noncomputable def invOK (TLB : List (List (List Nat))) (IV : Nat) : Bool :=
  CFSG.KC.Enum.allN (nat_lit 1024) fun e => eqB (bitB IV e) (invK (tabK TLB e))

@[expose] noncomputable def inBK (t B : List Nat) (K : Nat) : Bool :=
  andB (allL B fun v => Nat.beq (actK t v) v)
    (allR (nat_lit 11) fun j =>
      bitB K (Nat.xor (actK t (Nat.shiftLeft (nat_lit 1) j)) (Nat.shiftLeft (nat_lit 1) j)))

@[expose] noncomputable def cntK (TLB : List (List (List Nat))) (IV : Nat) (B : List Nat) (K : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e acc => strictN acc fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a)
      (andB (bitB IV e) (inBK (tabK TLB e) B K))) (nat_lit 1024)

@[expose] noncomputable def onlyIn (TK N I0 K : Nat) : Bool :=
  CFSG.KC.Enum.allN N fun i =>
    orB (notB (subK (keyK (octL (fld (nat_lit 80) TK i))) K)) (Nat.beq i I0)

@[expose] noncomputable def onlyAbove (TK N I0 K : Nat) : Bool :=
  CFSG.KC.Enum.allN N fun i =>
    orB (notB (subK K (keyK (octL (fld (nat_lit 80) TK i))))) (Nat.beq i I0)

@[expose] noncomputable def xOK (SB : List (List Nat)) (SBK : List Nat) (TLB : List (List (List Nat)))
    (IV TK N I0 b : Nat) : Bool :=
  strictB (getN (nat_lit 0) SBK b) fun K =>
    strictB (lenK (rowL SB b)) fun n =>
      orB (Nat.blt n (nat_lit 4))
        (strictB (Nat.mul (nat_lit 8) (cntK TLB IV (rowL SB b) K)) fun x =>
          andB (Nat.ble x (Nat.shiftLeft (nat_lit 1) n))
            (orB (notB (Nat.beq x (Nat.shiftLeft (nat_lit 1) n))) (onlyIn TK N I0 K)))

@[expose] noncomputable def aboveOK (SB : List (List Nat)) (SBK : List Nat) (TK N I0 b : Nat) : Bool :=
  orB (Nat.blt (lenK (rowL SB b)) (nat_lit 2)) (onlyAbove TK N I0 (getN (nat_lit 0) SBK b))

@[expose] noncomputable def wordImg (LR : List (List Nat)) (w : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun W => W)
    (fun l _ ih W => ih (mapK (rowL LR l) W)) w

end CFSG.KC.J4Loc

end
