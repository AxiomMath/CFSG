module

public import Certificates.Data.Kernel.Spor.PCount
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.MSyl

open CFSG.KC.Enum CFSG.KS.PCnt

@[expose] noncomputable def strictP (y : Nat) (k : Nat → List Nat × List Nat) : List Nat × List Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def getDN : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ d => d)
    (fun a _ ih i d => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j d) i)

@[expose] noncomputable def letP (I : Nat) (vs vis : List Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Nat.rec (motive := fun _ => Nat) (getDN vis (nat_lit 0) I) (fun j _ => getDN vs j I) k)
    (fun k => getDN vis k I) l

@[expose] noncomputable def letIP (I : Nat) (vs vis : List Nat) (l : Int) : Nat :=
  letP I vis vs l

@[expose] noncomputable def wordV (n w m I : Nat) (vs vis : List Nat) : List Int → Nat :=
  List.rec (motive := fun _ => Nat) I
    (fun l _ ih => strictN ih (fun R => pcomp n w m (letP I vs vis l) R))

@[expose] noncomputable def wordI (n w m I : Nat) (vs vis : List Nat) : List Int → Nat :=
  List.rec (motive := fun _ => Nat) I
    (fun l _ ih => strictN ih (fun R => pcomp n w m R (letIP I vs vis l)))

@[expose] noncomputable def slpRun (n w m I : Nat) :
    List (List Int) → List Nat → List Nat → List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat × List Nat) (fun vs vis => (vs, vis))
    (fun d _ ih vs vis => strictP (wordV n w m I vs vis d) (fun v =>
      strictP (wordI n w m I vs vis d) (fun vi => ih (vs ++ [v]) (vis ++ [vi]))))

@[expose] noncomputable def slpP (n w m I x xi y yi : Nat) (ds : List (List Int)) :
    List Nat × List Nat :=
  slpRun n w m I ds [x, y] [xi, yi]

@[expose] noncomputable def exprsV (n w m I : Nat) (S : List Nat × List Nat) (es : List (List Int)) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ ih => wordV n w m I S.1 S.2 e :: ih) es

@[expose] noncomputable def exprsI (n w m I : Nat) (S : List Nat × List Nat) (es : List (List Int)) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ ih => wordI n w m I S.1 S.2 e :: ih) es

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def clAdd (n w m y : Nat) : List Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun E => E)
    (fun g _ ih E => strictL (pcomp n w m y g) (fun z =>
      Bool.rec (motive := fun _ => List Nat) (ih (E ++ [z])) (ih E) (memB z E)))

@[expose] noncomputable def clRun (n w m : Nat) (gs : List Nat) (fuel : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ E => E)
    (fun _ ih h E => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ h) E)
      (ih (Nat.succ h) (clAdd n w m (getN E h) gs E)) (Nat.blt h E.length)) fuel

@[expose] noncomputable def closP (n w m I : Nat) (gs : List Nat) (cap : Nat) : List Nat :=
  clRun n w m gs cap (nat_lit 0) [I]

@[expose] noncomputable def closedP (n w m : Nat) (E gs : List Nat) : Bool :=
  allL (fun e => allL (fun g => memB (pcomp n w m e g) E) gs) E

@[expose] noncomputable def commAllP (n w m z : Nat) (gs : List Nat) : Bool :=
  allL (fun g => Nat.beq (pcomp n w m z g) (pcomp n w m g z)) gs

@[expose] noncomputable def sylowAutP (n w m I a ai b bi : Nat) (ds es : List (List Int))
    (z zi cap N k : Nat) : Bool :=
  strictB (Nat.shiftLeft (nat_lit 1) k) fun K =>
  (fun S => (fun pT pTi => (fun E =>
    bAnd(Nat.beq (pcomp n w m a ai) I, bAnd(Nat.beq (pcomp n w m b bi) I,
    bAnd(Nat.beq (pcomp n w m z zi) I,
    bAnd(closedP n w m E pT, bAnd(closedP n w m E pTi, bAnd(distB E,
    bAnd(Nat.beq E.length K, bAnd(Nat.beq (Nat.mod N K) (nat_lit 0),
    bAnd(Nat.beq (Nat.mod (Nat.div N K) (nat_lit 2)) (nat_lit 1),
    bAnd(memB a E, bAnd(memB z E, commAllP n w m z pT)))))))))))) (closP n w m I pT cap))
      (exprsV n w m I S es) (exprsI n w m I S es)) (slpP n w m I a ai b bi ds)

@[expose] noncomputable def powP (n w m I x : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) I (fun _ ih => strictN ih (fun y => pcomp n w m x y))

@[expose] noncomputable def ordLoop (n w m I x o : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih p d => bIf(Nat.beq d o, Nat.beq p I,
      bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq p I, false, true), true),
        strictB (pcomp n w m p x) (fun q => ih q (Nat.succ d)))))

@[expose] noncomputable def ordExP (n w m I x o : Nat) : Bool :=
  ordLoop n w m I x o o x (nat_lit 1)

@[expose] noncomputable def allEqP : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun v _ ih pT => List.rec (motive := fun _ => Bool) true (fun p t _ => bAnd(Nat.beq v p, ih t)) pT)

@[expose] noncomputable def survF (n w m I a ai b zb : Nat) (ds es : List (List Int)) (pT : List Nat)
    (r s mb h : Nat) : Nat :=
  nIf(bAnd(ordExP n w m I h mb,
    bAnd(ordExP n w m I (pcomp n w m a h) r,
    bAnd(ordExP n w m I
      (pcomp n w m a (pcomp n w m h (pcomp n w m a (powP n w m I h (Nat.sub mb (nat_lit 1)))))) s,
    bAnd(allEqP (exprsV n w m I (slpP n w m I a ai h (powP n w m I h (Nat.sub mb (nat_lit 1))) ds) es)
      pT,
    bAnd(bIf(Nat.beq h b, false, true), bIf(Nat.beq h zb, false, true)))))), nat_lit 1, nat_lit 0)

end CFSG.KS.MSyl

end
