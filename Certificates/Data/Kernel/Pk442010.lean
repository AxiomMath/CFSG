module

public import Certificates.Data.Kernel.A45Cls.Pock

public section

namespace CFSG.KC.Pk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.BfsPin

@[expose] def psK : List Nat := [0, 1, 3, 9]

@[expose] noncomputable def lnK (w L k : Nat) : Nat := Nat.land (Nat.shiftRight L (Nat.mul w k)) (mask w)

@[expose] noncomputable def ev (p i : Nat) : Nat := pg 6 (mask 6) p i

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 45 6 (mask 6) p q

@[expose] noncomputable def e2 (r p q : Nat) : Bool := eq2 45 6 (mask 6) r p q

@[expose] noncomputable def e22 (p q r s : Nat) : Bool := eq22 45 6 (mask 6) p q r s

@[expose] noncomputable def e32 (p q s r t : Nat) : Bool :=
  allN 45 fun i => Nat.beq (ev p (ev q (ev s i))) (ev r (ev t i))

@[expose] noncomputable def e23 (p q r s t : Nat) : Bool :=
  allN 45 fun i => Nat.beq (ev p (ev q i)) (ev r (ev s (ev t i)))

@[expose] noncomputable def invP (p q : Nat) : Bool := allN 45 fun i => Nat.beq (ev p (ev q i)) i

@[expose] noncomputable def cube1 (p : Nat) : Bool := allN 45 fun i => Nat.beq (ev p (ev p (ev p i))) i

@[expose] noncomputable def pow9 (p : Nat) : Bool := strictB (pc p (pc p p)) fun c => cube1 c

@[expose] noncomputable def isId (p : Nat) : Bool := isIdK 45 6 p

@[expose] noncomputable def idxK (N : Nat) (T S : Nat → Nat) (v : Nat) : Nat :=
  findK 45 6 psK T S (pkeyK 45 6 psK v) (nat_lit 24) (nat_lit 0) N

@[expose] noncomputable def memP (N : Nat) (T S : Nat → Nat) (v : Nat) : Bool := memK 45 6 psK N T S v

@[expose] noncomputable def mulC (c d : Nat) : Nat :=
  strictN (Nat.div c 27) fun a => strictN (Nat.mod (Nat.div c 9) 3) fun b =>
    strictN (Nat.mod (Nat.div c 3) 3) fun cc => strictN (Nat.mod c 3) fun dd =>
      strictN (Nat.div d 27) fun e => strictN (Nat.mod (Nat.div d 9) 3) fun f =>
        strictN (Nat.mod (Nat.div d 3) 3) fun g => strictN (Nat.mod d 3) fun h =>
          Nat.add (Nat.mul 27 (Nat.mod (Nat.add (Nat.mul a e) (Nat.mul b g)) 3))
            (Nat.add (Nat.mul 9 (Nat.mod (Nat.add (Nat.mul a f) (Nat.mul b h)) 3))
              (Nat.add (Nat.mul 3 (Nat.mod (Nat.add (Nat.mul cc e) (Nat.mul dd g)) 3))
                (Nat.mod (Nat.add (Nat.mul cc f) (Nat.mul dd h)) 3)))

@[expose] noncomputable def csAt (csW j : Nat) : Nat := lnK 7 csW j

@[expose] noncomputable def isCode (csW c : Nat) : Bool := exN 24 fun j => Nat.beq (csAt csW j) c

@[expose] noncomputable def homK (csW : Nat) (R : Nat → Nat) : Bool :=
  allN 24 fun i => strictB (csAt csW i) fun c => allN 24 fun j => strictB (csAt csW j) fun d =>
    bAnd(isCode csW (mulC c d), e2 (R (mulC c d)) (R c) (R d))

@[expose] noncomputable def injK (csW : Nat) (R : Nat → Nat) : Bool :=
  allN 24 fun i => strictB (csAt csW i) fun c => Nat.beq c 28 || !isId (R c)

@[expose] noncomputable def memRK (N : Nat) (T S : Nat → Nat) (csW : Nat) (R : Nat → Nat) : Bool :=
  allN 24 fun i => memP N T S (R (csAt csW i))

@[expose] noncomputable def hitK (csW : Nat) (R : Nat → Nat) (t : Nat) : Bool :=
  exN 24 fun i => Nat.beq (R (csAt csW i)) t

@[expose] noncomputable def subK (N : Nat) (T S : Nat → Nat) (Q : Nat → Nat) (t : Nat) : Bool :=
  allN 8 (fun j => memP N T S (Q j)) && exN 8 (fun j => isId (Q j)) &&
    exN 8 (fun j => Nat.beq (Q j) t) &&
    allN 8 (fun j => allN 8 fun k => exN 8 fun l => e2 (Q l) (Q j) (Q k)) &&
    allN 8 fun j => exN 8 fun k => invP (Q j) (Q k)

@[expose] noncomputable def centK (N : Nat) (T : Nat → Nat) (csW : Nat) (R Q : Nat → Nat) : Bool :=
  allN 24 (fun i => strictB (R (csAt csW i)) fun r => allN 8 fun j => e22 r (Q j) (Q j) r) &&
    allN N fun k => strictB (T k) fun x =>
      exN 8 (fun j => !e22 x (Q j) (Q j) x) || exN 24 fun i => Nat.beq (R (csAt csW i)) x

@[expose] noncomputable def conjK (csW : Nat) (R B : Nat → Nat) (g : Nat) : Bool :=
  invP g g && allN 24 fun i => strictB (csAt csW i) fun c => eq3 45 6 (mask 6) (B c) g (R c) g

@[expose] noncomputable def commK (csW : Nat) (R B : Nat → Nat) : Bool :=
  allN 24 (fun i => strictB (R (csAt csW i)) fun r =>
      allN 24 fun j => strictB (B (csAt csW j)) fun b => e22 r b b r) &&
    exN 24 fun i => strictB (R (csAt csW i)) fun r =>
      allN 24 fun j => !Nat.beq r (B (csAt csW j))

@[expose] noncomputable def nsK (N : Nat) (T Q : Nat → Nat) (t : Nat) : Bool :=
  allN N fun k => strictB (T k) fun x =>
    !cube1 x || allN 8 (fun j => e22 x (Q j) (Q j) x) ||
      allN 8 fun j => strictB (pc t (Q j)) fun tq =>
        exN 8 fun l => e32 (Q j) (Q l) x x (Q l) || e32 tq (Q l) x x (Q l)

@[expose] noncomputable def prodK (Q1 Q2 : Nat → Nat) (P : Nat) : Bool :=
  allN 32 fun a => strictB (lnK 6 P a) fun pa => allN a fun b => strictB (lnK 6 P b) fun pb =>
    !e22 (Q1 (Nat.div pa 8)) (Q2 (Nat.mod pa 8)) (Q1 (Nat.div pb 8)) (Q2 (Nat.mod pb 8))

@[expose] noncomputable def eL (W k : Nat) : Nat := lnK 13 W k

@[expose] noncomputable def eWK (N : Nat) (T : Nat → Nat) (csW : Nat) (R B : Nat → Nat) (W : Nat) :
    Bool :=
  allN N fun k => strictB (eL W k) fun v => Nat.beq v 0 ||
    strictB (Nat.sub v 1) fun u => strictB (Nat.div u 81) fun c => strictB (Nat.mod u 81) fun d =>
      bAnd(isCode csW c, bAnd(isCode csW d, e2 (T k) (R c) (B d)))

@[expose] noncomputable def eAllK (N : Nat) (T S : Nat → Nat) (csW : Nat) (R B : Nat → Nat) (W : Nat) :
    Bool :=
  allN 24 fun i => strictB (R (csAt csW i)) fun r => allN 24 fun j =>
    strictB (pc r (B (csAt csW j))) fun p => strictB (idxK N T S p) fun m =>
      bAnd(Nat.blt m N, bAnd(Nat.beq (T m) p, !Nat.beq (eL W m) 0))

@[expose] noncomputable def e9K (N : Nat) (T : Nat → Nat) (W : Nat) : Bool :=
  allN N fun k => !Nat.beq (eL W k) 0 || !pow9 (T k)

@[expose] noncomputable def eGK (N : Nat) (T S : Nat → Nat) (g W : Nat) : Bool :=
  allN N fun k => strictB (pc (T k) g) fun p => strictB (idxK N T S p) fun m =>
    bAnd(Nat.blt m N, bAnd(Nat.beq (T m) p,
      Bool.rec (motive := fun _ => Bool) (Nat.beq (eL W m) 0) (!Nat.beq (eL W m) 0)
        (Nat.beq (eL W k) 0)))

@[expose] noncomputable def noOddK (N : Nat) (T : Nat → Nat) (W : Nat) : Bool :=
  allN N fun k => strictB (T k) fun o => isId o || !cube1 o ||
    strictB (lnK 20 W k) fun v => bAnd(!Nat.beq v 0,
      strictB (Nat.sub v 1) fun u => strictB (Nat.mod u 1024) fun s =>
        strictB (Nat.div u 1024) fun s' => bAnd(Nat.blt s N, bAnd(Nat.blt s' N,
          bAnd(invP (T s) (T s'), !cube1 (pc o (pc (T s) (pc o (T s'))))))))

@[expose] noncomputable def ord9K (N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun k => strictB (T k) fun x => !pow9 x || cube1 x

@[expose] noncomputable def uAt (T : Nat → Nat) (U k : Nat) : Nat := T (lnK 7 U k)

@[expose] noncomputable def uK (N : Nat) (T : Nat → Nat) (U : Nat) : Bool :=
  allN 12 (fun k => Nat.blt (lnK 7 U k) N) &&
    allN 12 (fun a => allN a fun b => !Nat.beq (uAt T U a) (uAt T U b)) &&
    exN 12 (fun k => isId (uAt T U k)) &&
    allN 12 (fun a => allN 12 fun b => exN 12 fun c => e2 (uAt T U c) (uAt T U a) (uAt T U b)) &&
    allN 12 (fun a => exN 12 fun b => invP (uAt T U a) (uAt T U b)) &&
    allN N fun k => strictB (T k) fun x => !cube1 x || exN 12 fun c => Nat.beq (uAt T U c) x

@[expose] noncomputable def inQ8 (q a t ta b ba bt bta : Nat) : Bool :=
  isId q || Nat.beq q a || Nat.beq q t || Nat.beq q ta || Nat.beq q b || Nat.beq q ba ||
    Nat.beq q bt || Nat.beq q bta

@[expose] noncomputable def pairK (N : Nat) (T Q1 Q2 : Nat → Nat) (t : Nat) : Bool :=
  allN N fun i => strictB (T i) fun a => !e2 t a a || allN N fun j => strictB (T j) fun b =>
    !e2 t b b || !e23 b a t a b ||
      strictB (pc t a) fun ta => strictB (pc b a) fun ba => strictB (pc b t) fun bt =>
        strictB (pc b ta) fun bta =>
          allN 8 (fun k => inQ8 (Q1 k) a t ta b ba bt bta) ||
            allN 8 fun k => inQ8 (Q2 k) a t ta b ba bt bta

end CFSG.KC.Pk442010

end
