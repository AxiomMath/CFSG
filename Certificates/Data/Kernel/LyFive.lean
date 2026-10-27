
module

public import Certificates.Data.Kernel.LyOmega.Chart
public import CFSG.RankThree.Native.LyFiveDataBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.FiveFacts
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Sporadic.Schreier.LyChain11
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.KC.LyFive

open CFSG.KC.LyOm CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord CFSG.RankThree.Native

@[expose] noncomputable def strictL (v : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def wordF (C : BConsts) (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) C.ONEF (fun l rest _ => wordR (fMul C) G (G l) rest) w

@[expose] noncomputable def powF (C : BConsts) (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C.ONEF (fun _ acc => strictN acc (fun a => fMul C a X)) e

@[expose] noncomputable def pow5F (C : BConsts) (X : Nat) : Nat :=
  strictN (fMul C X X) (fun X2 => strictN (fMul C X2 X2) (fun X4 => fMul C X4 X))

@[expose] noncomputable def slpStepF (C : BConsts) (R : List Nat) : FiveIns → List Nat
  | .mu i j k => strictL (fMul C (R.getD i 0) (R.getD j 0)) (fun v => R.set k v)
  | .pwr e i k => strictL (powF C (R.getD i 0) e) (fun v => R.set k v)

@[expose] noncomputable def slpF (C : BConsts) (R : List Nat) (prog : List FiveIns) : List Nat :=
  prog.foldl (slpStepF C) R

@[expose] def abL (z : ℤ) : Nat := if z = 1 then 0 else if z = 2 then 1 else if z = -1 then 2 else 3

@[expose] def hL (l : Nat) : Nat := [29, 30, 36, 37].getD l 0

@[expose] def elW (n : Nat) : List Nat :=
  (if n / 3125 = 0 then [] else [n / 3125 - 1]) ++
    (if n % 3125 / 625 % 5 = 0 then [] else [16 + n % 3125 / 625 % 5 - 1]) ++
    (if n % 3125 / 125 % 5 = 0 then [] else [12 + n % 3125 / 125 % 5 - 1]) ++
    (if n % 3125 / 25 % 5 = 0 then [] else [8 + n % 3125 / 25 % 5 - 1]) ++
    (if n % 3125 / 5 % 5 = 0 then [] else [4 + n % 3125 / 5 % 5 - 1]) ++
    (if n % 5 = 0 then [] else [20 + n % 5 - 1])

@[expose] noncomputable def elF (C : BConsts) (G : Nat → Nat) (n : Nat) : Nat := wordF C G (elW n)

@[expose] noncomputable def edgeF (C : BConsts) (G : Nat → Nat) (cj : List Nat) (l Mp Mo : Nat) :
    Bool :=
  bIf(Nat.blt l (nat_lit 8),
    letB (G (cj.getD l 0)) (fun T => Nat.beq (fMul C T Mp) (fMul C Mo T)),
    Nat.beq (powF C Mp (Nat.sub l (nat_lit 6))) Mo)

@[expose] noncomputable def recF (TB : List Nat) (i o w : Nat) : Nat :=
  fldW (getRec (fun k => TB.getD k 0) (nat_lit 40) i) o w

@[expose] noncomputable def treeGo (C : BConsts) (G : Nat → Nat) (TB cj rt : List Nat) (NT : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun _ ih i pp Mp => bIf(Nat.blt i NT,
      letB (recF TB i (nat_lit 27) (nat_lit 7)) (fun l =>
        letB (recF TB i (nat_lit 0) (nat_lit 14)) (fun o => bAnd(Nat.blt o (nat_lit 15625),
          bIf(Nat.ble (nat_lit 100) l,
            bAnd(Nat.blt l (nat_lit 117),
              bAnd(Nat.beq o (rt.getD (Nat.sub l (nat_lit 100)) 0), ih (Nat.succ i) pp Mp)),
            letB (recF TB i (nat_lit 14) (nat_lit 13)) (fun p =>
              bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 11),
                bIf(Nat.beq p pp,
                  bAnd(edgeF C G cj l Mp (elF C G o), ih (Nat.succ i) pp Mp),
                  letB (elF C G (recF TB p (nat_lit 0) (nat_lit 14))) (fun Mq =>
                    bAnd(edgeF C G cj l Mq (elF C G o), ih (Nat.succ i) p Mq)))))))))),
      true))

@[expose] noncomputable def treeBlk (C : BConsts) (G : Nat → Nat) (TB cj rt : List Nat) (NT k : Nat) :
    Bool :=
  treeGo C G TB cj rt NT (nat_lit 64) (Nat.mul (nat_lit 64) k) (nat_lit 16383) (nat_lit 0)

@[expose] noncomputable def posF (PB : List Nat) (n : Nat) : Nat :=
  getRec (fun k => PB.getD k 0) (nat_lit 14) n

@[expose] noncomputable def posOK (TB PB : List Nat) (NT : Nat) : Bool :=
  allBelow (nat_lit 15625) (nat_lit 245) (fun n => letB (posF PB n) (fun q =>
    bIf(Nat.beq q (nat_lit 16383),
      bIf(Nat.beq n (nat_lit 0), true,
        bAnd(Nat.ble (nat_lit 3125) n, Nat.beq (posF PB (Nat.sub n (Nat.mod n (nat_lit 5))))
          (nat_lit 16383))),
      bAnd(Nat.blt q NT, Nat.beq (recF TB q (nat_lit 0) (nat_lit 14)) n))))

@[expose] noncomputable def baseF (C : BConsts) (G : Nat → Nat) (PB : List Nat) (b : Nat) : Bool :=
  bIf(Nat.beq (posF PB b) (nat_lit 16383), notB (Nat.beq (pow5F C (elF C G b)) C.ONEF), true)

@[expose] noncomputable def baseBlk (C : BConsts) (G : Nat → Nat) (PB : List Nat) (c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih => bAnd(baseF C G PB
      (Nat.add (Nat.mul (nat_lit 3125) (Nat.add (nat_lit 1) (Nat.div c (nat_lit 25))))
        (Nat.mul (nat_lit 5) (Nat.add (Nat.mul (nat_lit 25) (Nat.mod c (nat_lit 25))) t))), ih))
    (nat_lit 25)

end CFSG.KC.LyFive

end
