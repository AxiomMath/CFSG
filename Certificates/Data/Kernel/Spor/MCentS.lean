module

public import Certificates.Data.Kernel.Spor.MCount

public section

namespace CFSG.KS.MCent

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def cSrch (n w m nw pm : Nat) (tst : Nat → Nat → Bool) (leaf : Nat → Bool) :
    Nat → List Nat → Nat → Nat
  | _, [], p => nIf(leaf p, nat_lit 1, nat_lit 0)
  | l, L :: Ls, p => foldUp (lcnt L) (fun k s => strictN (pcomp n w m p (ltr nw pm L k)) (fun q =>
      nIf(tst l q, Nat.add s (cSrch n w m nw pm tst leaf (Nat.succ l) Ls q), s))) (nat_lit 0)

@[expose] noncomputable def tstC (w m G' : Nat) (bs : List Nat) (D : List (List (Nat × Nat × Nat)))
    (l q : Nat) : Bool :=
  (D.getD l []).all fun t => Nat.beq (MEnum.itr (fun z => pg w m G' z) t.2.1
    (pg w m q (bs.getD t.1 0))) (pg w m q (bs.getD t.2.2 0))

@[expose] noncomputable def leafC (n w m G G' q : Nat) : Bool :=
  MEnum.allFrom (fun x => Nat.beq (pg w m q (pg w m G x)) (pg w m G' (pg w m q x))) n (nat_lit 0)

@[expose] noncomputable def trOKC (w m G : Nat) (bs : List Nat) (D : List (List (Nat × Nat × Nat))) :
    Bool :=
  (List.range D.length).all fun l => (D.getD l []).all fun t =>
    bAnd(Nat.ble t.1 l, bAnd(Nat.ble t.2.2 l, Nat.beq (MEnum.itr (fun z => pg w m G z) t.2.1
      (bs.getD t.1 0)) (bs.getD t.2.2 0)))

@[expose] noncomputable def cntCM (n w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (G G' : Nat) (D : List (List (Nat × Nat × Nat))) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (MEnum.mLT n w tA tB W) (fun LT =>
  MEnum.levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    cSrch n w m nw pm (tstC w m G' bs D) (leafC n w m G G') 0 Ls idn)))))))

@[expose] noncomputable def wdP (n w m A B : Nat) : List Nat → Nat
  | [] => pidn n w
  | c :: l => strictN (wdP n w m A B l) (fun q => pcomp n w m (nIf(Nat.beq c 0, A, B)) q)

@[expose] noncomputable def jobC (n w m nw pm idn A B : Nat) (bs : List Nat) (RW : List (List Nat))
    (Ls : List Nat) (j : Nat × Nat × List (List (Nat × Nat × Nat)) × Nat) : Bool :=
  strictB (wdP n w m A B (RW.getD j.1 [])) (fun G => strictB (wdP n w m A B (RW.getD j.2.1 []))
    (fun G' => bAnd(trOKC w m G bs j.2.2.1, Nat.beq (cSrch n w m nw pm (tstC w m G' bs j.2.2.1)
      (leafC n w m G G') 0 Ls idn) j.2.2.2)))

@[expose] noncomputable def centJobsOK (n w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (RW : List (List Nat))
    (JB : List (Nat × Nat × List (List (Nat × Nat × Nat)) × Nat)) : Bool :=
  Nat.beq (strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (MEnum.mLT n w tA tB W) (fun LT =>
  strictN (M11.packL w tA) (fun A => strictN (M11.packL w tB) (fun B =>
  MEnum.levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    nIf(JB.all (jobC n w m nw pm idn A B bs RW Ls), nat_lit 1, nat_lit 0)))))))))))
    (nat_lit 1)

@[expose] noncomputable def pcolC (n w m r s Y Yi : Nat) (S : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => strictN ih (fun c =>
    nIf(MEnum.pairOKG n w m r s x x Y Yi, Nat.succ c, c))) S

@[expose] noncomputable def repOrdPairOK (n w r s ky : Nat) (tA tB : List Nat) (RW : List (List Nat))
    (OR PC S : List Nat) : Bool :=
  strictB (mask w) (fun m => strictB (M11.packL w tA) (fun A => strictB (M11.packL w tB) (fun B =>
    (List.range RW.length).all fun i => strictB (wdP n w m A B (RW.getD i [])) (fun G =>
      strictB (M11.ordC n w m G) (fun o => bAnd(Nat.beq o (OR.getD i 0),
        bIf(Nat.beq o ky, Nat.beq (pcolC n w m r s G (pinvS n w m G) S) (PC.getD i 0), true)))))))

end CFSG.KS.MCent

end
