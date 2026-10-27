module

public import Certificates.Data.Kernel.F4M3B

public section

namespace CFSG.KC.F4T7B

open CFSG.KC.F4M3B

variable {α : Type}

@[expose] def zr (o : Ops α) : α := o.x o.t o.t

@[expose] def sel (o : Ops α) (b : Bool) (p : α) : α := cond b p (zr o)

@[expose] def lit (o : Ops α) (b : Bool) (p : α) : α := cond b p (bnot o p)

@[expose] def cl (c : Nat) : Bool := Nat.testBit c 0

@[expose] def ch (c : Nat) : Bool := Nat.testBit c 1

@[expose] def kl (o : Ops α) (c : Nat) (l h : α) : α := o.x (sel o (cl c) l) (sel o (ch c) h)

@[expose] def kh (o : Ops α) (c : Nat) (l h : α) : α :=
  o.x (o.x (sel o (ch c) l) (sel o (cl c) h)) (sel o (ch c) h)

@[expose] def fmul (a b : Nat) : Nat :=
  cond (xor (cl a && cl b) (ch a && ch b)) 1 0 +
    cond (xor (xor (cl a && ch b) (ch a && cl b)) (ch a && ch b)) 2 0

abbrev Pt := Nat × Nat × Nat

@[expose] def smul (c : Nat) (u : Pt) : Pt := (fmul c u.1, fmul c u.2.1, fmul c u.2.2)

structure VT (α : Type) where
  l0 : α
  h0 : α
  l1 : α
  h1 : α
  l2 : α
  h2 : α

@[expose] def img (o : Ops α) (A : MatT α) (u : Pt) : VT α :=
  ⟨o.x (o.x (kl o u.1 A.l00 A.h00) (kl o u.2.1 A.l01 A.h01)) (kl o u.2.2 A.l02 A.h02),
    o.x (o.x (kh o u.1 A.l00 A.h00) (kh o u.2.1 A.l01 A.h01)) (kh o u.2.2 A.l02 A.h02),
    o.x (o.x (kl o u.1 A.l10 A.h10) (kl o u.2.1 A.l11 A.h11)) (kl o u.2.2 A.l12 A.h12),
    o.x (o.x (kh o u.1 A.l10 A.h10) (kh o u.2.1 A.l11 A.h11)) (kh o u.2.2 A.l12 A.h12),
    o.x (o.x (kl o u.1 A.l20 A.h20) (kl o u.2.1 A.l21 A.h21)) (kl o u.2.2 A.l22 A.h22),
    o.x (o.x (kh o u.1 A.l20 A.h20) (kh o u.2.1 A.l21 A.h21)) (kh o u.2.2 A.l22 A.h22)⟩

@[expose] def eqV (o : Ops α) (w : VT α) (e : Pt) : α :=
  o.a (o.a (o.a (lit o (cl e.1) w.l0) (lit o (ch e.1) w.h0))
    (o.a (lit o (cl e.2.1) w.l1) (lit o (ch e.2.1) w.h1)))
    (o.a (lit o (cl e.2.2) w.l2) (lit o (ch e.2.2) w.h2))

@[expose] def mulOf (o : Ops α) (w : VT α) (u : Pt) : α :=
  bor o (bor o (eqV o w (smul 1 u)) (eqV o w (smul 2 u))) (eqV o w (smul 3 u))

@[expose] def mtab (o : Ops α) (A : MatT α) (om : List Pt) : List (List α) :=
  om.map fun u => om.map (mulOf o (img o A u))

@[expose] def orL (o : Ops α) (l : List α) : α := l.foldr (bor o) (zr o)

@[expose] def andL (o : Ops α) (l : List α) : α := l.foldr o.a o.t

@[expose] def stabT (o : Ops α) (T : List (List α)) : α := andL o (T.map (orL o))

@[expose] def kerT (o : Ops α) (T : List (List α)) : α :=
  andL o ((List.range 6).map fun k => (T.getD k []).getD k (zr o))

@[expose] def before (o : Ops α) (r : List α) (j : Nat) : α := orL o (r.take j)

@[expose] def invP (o : Ops α) (rk rl : List α) : α :=
  orL o ((List.range 6).map fun j => o.a (rk.getD j (zr o)) (before o rl j))

@[expose] def parT (o : Ops α) (T : List (List α)) : α :=
  ((List.range 6).flatMap fun k => (List.range 6).filterMap fun l =>
    if k < l then some (invP o (T.getD k []) (T.getD l [])) else none).foldr o.x (zr o)

@[expose] def invT (o : Ops α) (T U : List (List α)) : α :=
  andL o ((List.range 6).flatMap fun k => (List.range 6).map fun j =>
    o.a (bor o (bnot o ((T.getD k []).getD j (zr o))) ((U.getD j []).getD k (zr o)))
      (bor o (bnot o ((U.getD k []).getD j (zr o))) ((T.getD j []).getD k (zr o))))

@[expose] def ml (o : Ops α) (a0 a1 b0 b1 c0 c1 d0 d1 : α) : α :=
  o.x (pl o a0 a1 b0 b1) (pl o c0 c1 d0 d1)

@[expose] def mh (o : Ops α) (a0 a1 b0 b1 c0 c1 d0 d1 : α) : α :=
  o.x (ph o a0 a1 b0 b1) (ph o c0 c1 d0 d1)

@[expose] def adjT (o : Ops α) (A : MatT α) : MatT α :=
  ⟨ml o A.l11 A.h11 A.l22 A.h22 A.l12 A.h12 A.l21 A.h21,
    mh o A.l11 A.h11 A.l22 A.h22 A.l12 A.h12 A.l21 A.h21,
    ml o A.l01 A.h01 A.l22 A.h22 A.l02 A.h02 A.l21 A.h21,
    mh o A.l01 A.h01 A.l22 A.h22 A.l02 A.h02 A.l21 A.h21,
    ml o A.l01 A.h01 A.l12 A.h12 A.l02 A.h02 A.l11 A.h11,
    mh o A.l01 A.h01 A.l12 A.h12 A.l02 A.h02 A.l11 A.h11,
    ml o A.l10 A.h10 A.l22 A.h22 A.l12 A.h12 A.l20 A.h20,
    mh o A.l10 A.h10 A.l22 A.h22 A.l12 A.h12 A.l20 A.h20,
    ml o A.l00 A.h00 A.l22 A.h22 A.l02 A.h02 A.l20 A.h20,
    mh o A.l00 A.h00 A.l22 A.h22 A.l02 A.h02 A.l20 A.h20,
    ml o A.l00 A.h00 A.l12 A.h12 A.l02 A.h02 A.l10 A.h10,
    mh o A.l00 A.h00 A.l12 A.h12 A.l02 A.h02 A.l10 A.h10,
    ml o A.l10 A.h10 A.l21 A.h21 A.l11 A.h11 A.l20 A.h20,
    mh o A.l10 A.h10 A.l21 A.h21 A.l11 A.h11 A.l20 A.h20,
    ml o A.l00 A.h00 A.l21 A.h21 A.l01 A.h01 A.l20 A.h20,
    mh o A.l00 A.h00 A.l21 A.h21 A.l01 A.h01 A.l20 A.h20,
    ml o A.l00 A.h00 A.l11 A.h11 A.l01 A.h01 A.l10 A.h10,
    mh o A.l00 A.h00 A.l11 A.h11 A.l01 A.h01 A.l10 A.h10⟩

@[expose] def stabX (o : Ops α) (A : MatT α) (om : List Pt) : α :=
  o.a (isOne o (detL o A) (detH o A)) (stabT o (mtab o A om))

@[expose] def badX (o : Ops α) (A : MatT α) (om : List Pt) : α :=
  bor o (bor o (bnot o (stabT o (mtab o (adjT o A) om)))
    (bnot o (invT o (mtab o A om) (mtab o (adjT o A) om)))) (parT o (mtab o A om))

@[expose] def sumPow (C : List Nat) : Nat := C.foldr (fun c acc => Nat.lor (Nat.shiftLeft 1 c) acc) 0

@[expose] def incB (C : List Nat) : Bool :=
  (C.foldr (fun c (acc : Bool × Nat) => (acc.1 && Nat.blt c acc.2, c)) (true, 262144)).1

@[expose] def chkI (t : Nat) (P : MatT Nat) (om : List Pt) (C K : List Nat) : Bool :=
  let o := natOps t
  let X := stabX o P om
  let Kp := o.a X (kerT o (mtab o P om))
  incB C && incB K && Nat.beq X (sumPow C) && Nat.beq Kp (sumPow K) &&
    Nat.beq (o.a X (badX o P om)) 0 && Nat.beq (o.a Kp (bnot o (scal o P))) 0

@[expose] noncomputable def chkAll (om : List Pt) (C K : List Nat) : Bool :=
  frc (Nat.sub (Nat.pow 2 (Nat.pow 2 18)) 1) fun t => plnK 18 fun P => chkI t P om C K

@[expose] def omC : Nat → List Pt
  | 0 => [(1, 1, 1), (1, 3, 3), (1, 2, 3), (1, 1, 2), (1, 3, 2), (1, 2, 1)]
  | 1 => [(0, 0, 1), (1, 2, 2), (0, 1, 0), (1, 0, 0), (1, 1, 3), (1, 3, 1)]
  | 2 => [(0, 0, 1), (1, 3, 3), (1, 0, 0), (1, 2, 1), (1, 1, 2), (0, 1, 0)]
  | 3 => [(1, 1, 1), (1, 3, 1), (1, 1, 3), (1, 2, 3), (1, 3, 2), (1, 2, 2)]
  | 4 => [(1, 1, 2), (1, 3, 3), (1, 2, 1), (1, 1, 3), (1, 2, 2), (1, 3, 1)]
  | 5 => [(0, 0, 1), (1, 2, 3), (1, 3, 2), (1, 1, 1), (1, 0, 0), (0, 1, 0)]
  | _ => []

end CFSG.KC.F4T7B

end
