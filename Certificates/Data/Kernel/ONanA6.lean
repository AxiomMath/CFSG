module

public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.ONanA6

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def I10 : Nat := nat_lit 325702574508064

@[expose] noncomputable def nonEmpty (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) l

@[expose] noncomputable def prodL (L R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun y _ ih => List.rec (motive := fun _ => List Nat) ih
      (fun r _ ih2 => List.cons (mul 10 y r) ih2) R) L

@[expose] noncomputable def zipAll (L G : List Nat) (f : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun G => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) G)
    (fun x _ ih G => List.rec (motive := fun _ => Bool) false (fun g gs _ => andB (f x g) (ih gs)) G)
    L G

@[expose] noncomputable def cubeOne (y : Nat) : Bool :=
  letB y fun y => Nat.beq (mul 10 (mul 10 y y) y) I10

@[expose] noncomputable def withNine (u u3 r : Nat) (f : List Nat → Bool) : Bool :=
  letB (mul 10 (mul 10 u r) u3) fun s => letB (mul 10 r r) fun r2 => letB (mul 10 s s) fun s2 =>
    letB (mul 10 r s) fun a => letB (mul 10 r s2) fun b => letB (mul 10 r2 s) fun c =>
      letB (mul 10 r2 s2) fun d => f [I10, s, s2, r, a, b, r2, c, d]

@[expose] noncomputable def eOfK (u2 x : Nat) : Nat := mul 10 (mul 10 x u2) (mul 10 x x)

@[expose] noncomputable def cAut (LA L R : List Nat) : Bool := eqLs LA (prodL L R)

@[expose] noncomputable def expB (b : Nat) : Bool :=
  letB (mul 10 b b) fun b2 => letB (mul 10 b2 b2) fun b4 => letB (mul 10 b4 b4) fun b8 =>
    letB (mul 10 (mul 10 b8 b8) b8) fun b24 => letB (mul 10 b24 b24) fun b48 =>
      Nat.beq (mul 10 (mul 10 b48 b48) b24) I10

@[expose] noncomputable def cExp (LA : List Nat) : Bool := allL LA expB

@[expose] noncomputable def ordRow (L : List Nat) (u x g : Nat) : Bool :=
  letB (mul 10 x x) fun x2 => letB (mul 10 x2 x) fun x3 => letB (mul 10 x2 x2) fun x4 =>
    andB (impB (Nat.beq (mul 10 x3 x3) I10) (orB (Nat.beq x2 I10) (Nat.beq x3 I10)))
      (andB (impB (Nat.beq (mul 10 x4 x4) I10) (Nat.beq x4 I10))
        (impB (andB (Nat.beq x4 I10) (notB (Nat.beq x2 I10)))
          (andB (memL g L) (Nat.beq (mul 10 g u) (mul 10 x g)))))

@[expose] noncomputable def cOrd (L G : List Nat) (u : Nat) : Bool := zipAll L G (ordRow L u)

@[expose] noncomputable def cU (u u2 u3 : Nat) : Bool :=
  andB (Nat.beq I10 (one 10)) (andB (Nat.beq u2 (mul 10 u u)) (Nat.beq u3 (mul 10 u2 u)))

@[expose] noncomputable def pcK (u u2 u3 r : Nat) : Bool :=
  andB (notB (Nat.beq r I10)) (letB (mul 10 r r) fun r2 => andB (Nat.beq (mul 10 r2 r) I10)
    (letB (mul 10 (mul 10 u r) u3) fun s => andB (Nat.beq (mul 10 s r) (mul 10 r s))
      (Nat.beq (mul 10 (mul 10 u2 r) u2) r2)))

@[expose] noncomputable def cPc (L PC : List Nat) (u u2 u3 : Nat) : Bool :=
  andB (eqLs PC (filtL L (pcK u u2 u3))) (nonEmpty PC)

@[expose] noncomputable def cDist (PC : List Nat) (u u3 : Nat) : Bool :=
  allL PC fun r => withNine u u3 r distinctL

@[expose] noncomputable def dcK (u d : Nat) : Bool :=
  andB (Nat.beq (mul 10 d d) I10)
    (andB (notB (Nat.beq d I10)) (Nat.beq (mul 10 (mul 10 (mul 10 d u) d) u) I10))

@[expose] noncomputable def cDs (L DS : List Nat) (u : Nat) : Bool :=
  andB (eqLs DS (filtL L (dcK u))) (nonEmpty DS)

@[expose] noncomputable def cEs (PC ES : List Nat) (u u2 u3 : Nat) : Bool :=
  allL PC fun r => withNine u u3 r fun l => allL l fun x => memL (eOfK u2 x) ES

@[expose] noncomputable def cRelA (PC DS : List Nat) (u u2 u3 : Nat) : Bool :=
  allL DS fun d => allL PC fun r => withNine u u3 r fun l =>
    anyL l fun x => cubeOne (mul 10 d (eOfK u2 x))

@[expose] noncomputable def relK (b d e : Nat) : Bool :=
  letB (inv 10 b) fun bi => letB (mul 10 b b) fun b2 => letB (mul 10 bi bi) fun b2i =>
    letB (mul 10 e d) fun ed =>
      Nat.beq (mul 10 (mul 10 (mul 10 (mul 10 (mul 10 (mul 10 b2 b) ed) (mul 10 b2i bi))
        (mul 10 (mul 10 b2 (mul 10 d e)) b2i)) (mul 10 (mul 10 b ed) bi)) d) I10

@[expose] noncomputable def bcK (GC : List Nat) (u u2 d b : Nat) : Bool :=
  andB (Nat.beq (mul 10 b d) (mul 10 (mul 10 u d) b))
    (letB (mul 10 b b) fun b2 => allL GC fun x => Nat.beq (mul 10 b2 x) (mul 10 (mul 10 (mul 10 u2 x) u2) b2))

@[expose] noncomputable def relBK (GC DS ES : List Nat) (u u2 b : Nat) : Bool :=
  allL DS fun d => impB (bcK GC u u2 d b) (letB (mul 10 u2 b) fun c =>
    allL ES fun e => impB (cubeOne (mul 10 d e)) (orB (relK b d e) (relK c d e)))

@[expose] noncomputable def fixK (PC GC DS ES : List Nat) (u u2 u3 b : Nat) : Bool :=
  letB (mul 10 b u) fun bu =>
    andB (impB (andB (notB (Nat.beq b I10)) (Nat.beq bu (mul 10 u b)))
        (allL PC fun r => notB (Nat.beq (mul 10 b r) (mul 10 r b))))
      (impB (Nat.beq bu (mul 10 u3 b)) (relBK GC DS ES u u2 b))

@[expose] noncomputable def cFix (LA PC GC DS ES : List Nat) (u u2 u3 : Nat) : Bool :=
  allL LA (fixK PC GC DS ES u u2 u3)

@[expose] noncomputable def c6151 (L R GC LA G PC DS ES : List Nat) (u u2 u3 : Nat) : Bool := allBs
  [cAut LA L R, cExp LA, cOrd L G u, cU u u2 u3, cPc L PC u u2 u3, cDist PC u u3, cDs L DS u,
   cEs PC ES u u2 u3, cRelA PC DS u u2 u3, cFix LA PC GC DS ES u u2 u3]

end CFSG.KC.ONanA6

end
