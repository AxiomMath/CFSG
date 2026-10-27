module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.Kernel.Fi22.Cent

public section

namespace CFSG.KC.Fi23C

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KS.Fi22Cent

@[expose] noncomputable def uF (G : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ ih k y => nIf(Nat.beq k (nat_lit 0), y,
      strictN (ih (tb G (nat_lit 91) k) y) fun z =>
        nIf(Nat.beq (tb G (nat_lit 92) k) (nat_lit 1), tb G (nat_lit 39) z, tb G (nat_lit 40) z))) f

@[expose] noncomputable def uInvF (G : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      ih (tb G (nat_lit 91) k)
        (nIf(Nat.beq (tb G (nat_lit 92) k) (nat_lit 1), tb G (nat_lit 39) x, tb G (nat_lit 41) x)))) f

@[expose] noncomputable def cJ (G : Nat → Nat) (k x : Nat) : Nat :=
  uF G (nat_lit 31671) k (strictN (uInvF G (nat_lit 31671) k x) (tb G (nat_lit 43)))

@[expose] noncomputable def eaK (G H : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 3510) fun i => strictB (tb H (nat_lit 0) i) fun k =>
      bAnd(Nat.blt (nat_lit 0) k, bAnd(Nat.blt k (nat_lit 31671),
        bAnd(Nat.beq (tb G (nat_lit 43) k) k, Nat.beq (tb H (nat_lit 1) k) i))),
    allN (nat_lit 3509) fun i => Nat.blt (tb H (nat_lit 0) i) (tb H (nat_lit 0) (Nat.succ i)))

@[expose] noncomputable def epK (G H : Nat → Nat) : Bool :=
  allN (nat_lit 31671) fun x => strictB (tb H (nat_lit 1) x) fun m =>
    bIf(Nat.blt m (nat_lit 3510), Nat.beq (tb H (nat_lit 0) m) x,
      bAnd(Nat.beq m (nat_lit 3510),
        bIf(Nat.beq x (nat_lit 0), true, Bool.not (Nat.beq (tb G (nat_lit 43) x) x))))

@[expose] noncomputable def phiK (H : Nat → Nat) : Bool :=
  allN (nat_lit 3510) fun i =>
    bAnd(Nat.blt (tb H (nat_lit 2) i) (nat_lit 3510), bAnd(Nat.blt (tb H (nat_lit 3) i) (nat_lit 3510),
      bAnd(Nat.beq (tb H (nat_lit 3) (tb H (nat_lit 2) i)) i,
        Nat.beq (tb H (nat_lit 2) (tb H (nat_lit 3) i)) i)))

@[expose] noncomputable def d2K (G : Nat → Nat) : Bool :=
  allN (nat_lit 31671) fun x => Nat.beq (tb G (nat_lit 43) (tb G (nat_lit 43) x)) x

@[expose] noncomputable def rowAt (G H : Nat → Nat) (r s j : Nat) : Bool :=
  strictB (tb H (nat_lit 8) s) fun g => strictB (cJ G (tb H (nat_lit 0) g) (tb H (nat_lit 0) j))
    fun x => strictB (tb H (nat_lit 1) x) fun m =>
      bAnd(Nat.blt g (nat_lit 3510), bAnd(Nat.blt m (nat_lit 3510),
        bAnd(Nat.beq (tb H (nat_lit 0) m) x,
          Nat.beq (tb H r m) (cK (tb H r g) (tb H r j)))))

@[expose] noncomputable def rowSl (G H : Nat → Nat) (r s : Nat) : Bool :=
  allN (nat_lit 3510) (rowAt G H r s)

@[expose] noncomputable def treeK (G H : Nat → Nat) : Bool :=
  bAnd(Nat.beq (tb H (nat_lit 4) (nat_lit 0)) (tb H (nat_lit 8) (nat_lit 0)),
  bAnd(allN (nat_lit 3510) fun t => bAnd(Nat.blt (tb H (nat_lit 4) t) (nat_lit 3510),
      bIf(Nat.beq t (nat_lit 0), true,
        strictB (tb H (nat_lit 6) t) fun s => strictB (tb H (nat_lit 7) t) fun g =>
          bAnd(Nat.blt s t, bAnd(Nat.blt g (nat_lit 7),
            Nat.beq (cJ G (tb H (nat_lit 0) (tb H (nat_lit 8) g)) (tb H (nat_lit 0) (tb H (nat_lit 4) s)))
              (tb H (nat_lit 0) (tb H (nat_lit 4) t)))))),
    allN (nat_lit 3510) fun i =>
      bAnd(Nat.blt (tb H (nat_lit 5) i) (nat_lit 3510), Nat.beq (tb H (nat_lit 4) (tb H (nat_lit 5) i)) i)))

@[expose] noncomputable def swK (H : Nat → Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun k _ ih => bAnd(Nat.blt (tb H (nat_lit 1) k) (nat_lit 3510),
      bAnd(Nat.beq (tb H (nat_lit 0) (tb H (nat_lit 1) k)) k, ih))) w

@[expose] noncomputable def wordJ (G : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => cJ G k ih) w

@[expose] noncomputable def powK (G : Nat → Nat) (w : List Nat) (m : Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(Nat.beq (itK (wordJ G w) m q) (tb G (nat_lit 43) q), ih)) Q

@[expose] noncomputable def hList (H : Nat → Nat) (r : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | j, c + 1 => tb H r j :: hList H r (j + 1) c

@[expose] def digs : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n < 10 then [48 + n] else digs f (n / 10) ++ [48 + n % 10]

@[expose] def render : List Nat → List Nat
  | [] => []
  | [n] => digs 6 n
  | n :: m :: l => digs 6 n ++ 32 :: render (m :: l)

end CFSG.KC.Fi23C

end
