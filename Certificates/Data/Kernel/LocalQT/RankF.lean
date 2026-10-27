module

public import Certificates.Data.Kernel.LocalQT.RankW

public section

namespace CFSG.KC.LQT.RF

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.RW

structure EF where
  kt : TT
  cnt : Nat
  par : List Nat
  cl : List Nat
  fr : List Nat

@[expose] noncomputable def letF (y : Nat) (k : Nat → EF) : EF :=
  Nat.rec (motive := fun _ => EF) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def kidsF (n w : Nat) (G : List Nat) (i x : Nat) (st : EF) : EF :=
  List.rec (motive := fun _ => EF → EF) (fun st => st)
    (fun s _ ih st => letF (mulW n w s x) fun c =>
      ih (Bool.rec (motive := fun _ => EF)
        (letF (Nat.succ st.cnt) fun cnt' =>
          EF.mk (insTT st.kt c st.cnt []) cnt' (List.cons i st.par) (List.cons st.cnt st.cl)
            (List.cons c st.fr))
        (letF (idxTT st.kt c) fun j => EF.mk st.kt st.cnt st.par (List.cons j st.cl) st.fr)
        (memTT st.kt c))) G st

@[expose] noncomputable def roundF (n w gi : Nat) (G F : List Nat) (i : Nat) (st : EF) : EF :=
  List.rec (motive := fun _ => Nat → EF → EF) (fun _ st => st)
    (fun x _ ih i st => letF (Nat.succ i) fun i' => ih i'
      ((fun (st' : EF) => EF.mk st'.kt st'.cnt st'.par (zerosOn gi st'.cl) st'.fr)
        (kidsF n w G i x st))) F i st

@[expose] noncomputable def enumF (n w gi : Nat) (G : List Nat) (dd : Nat) : EF × Nat × List Nat :=
  Nat.rec (motive := fun _ => EF × Nat × List Nat)
    (Prod.mk (EF.mk (insTT TT.lf (oneW n w) 0 []) 1 [0] [] []) (Prod.mk 0 [oneW n w]))
    (fun _ ih => Prod.rec (motive := fun _ => EF × Nat × List Nat) (fun st p =>
      Prod.rec (motive := fun _ => EF × Nat × List Nat) (fun i F =>
        (fun (st' : EF) => Prod.mk (EF.mk st'.kt st'.cnt st'.par st'.cl [])
            (Prod.mk st.cnt (revOn st'.fr [])))
          (roundF n w gi G F i (EF.mk st.kt st.cnt st.par st.cl []))) p) ih) dd

@[expose] noncomputable def enumT (n w : Nat) (ta tb : List Nat) (prog qp : List (Nat × Nat))
    (dd : Nat) : EF × Nat × List Nat :=
  enumF n w (lenA qp) (fstN (slpW n w (codeK w ta) (codeK w tb) prog) qp) dd

@[expose] noncomputable def mulF (W g : Nat) (E : EF × Nat × List Nat) : Nat → Nat → Nat :=
  mulIdxW W g (Nat.add g g) (codeK W (revOn E.1.par [])) (codeK W (revOn E.1.cl [])) E.1.cnt

@[expose] noncomputable def invsF (W g : Nat) (E : EF × Nat × List Nat) : List Nat :=
  filterN E.1.cnt fun i => andB (notB (Nat.beq i 0)) (Nat.beq (mulF W g E i i) 0)

@[expose] noncomputable def branchF (mul : Nat → Nat → Nat) (invs : List Nat) (z d c : Nat) :
    Bool :=
  notB (andB (andB (notB (hasW [0, z] c)) (Nat.beq (mul c z) (mul z c)))
    (dfsW mul invs d [c, z] (appK [0, z] (mapW (mul c) [0, z]))))

@[expose] noncomputable def rankFH (n w W : Nat) (ta tb : List Nat) (prog qp : List (Nat × Nat))
    (k fuel dd zi K L : Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    ((fun (R : List Nat) => andB (qpW n w [] R qp)
      ((fun (E : EF × Nat × List Nat) => allBs [
          List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) E.2.2,
          Nat.ble E.1.cnt fuel, Nat.beq E.1.cnt (Nat.pow 2 k),
          allL E.1.par (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
          allL E.1.cl (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
          Nat.blt zi E.1.cnt, notB (Nat.beq zi 0), Nat.beq (mulF W (lenA qp) E zi zi) 0,
          allR 0 E.1.cnt (fun i => Nat.beq (mulF W (lenA qp) E zi i) (mulF W (lenA qp) E i zi)),
          Nat.ble (lenA (invsF W (lenA qp) E)) (Nat.mul K L)])
        (enumF n w (lenA qp) (fstN R qp) dd)))
    (slpW n w (codeK w ta) (codeK w tb) prog))))

@[expose] noncomputable def rankFP (n w W : Nat) (ta tb : List Nat) (prog qp : List (Nat × Nat))
    (d dd zi lo len : Nat) : Bool :=
  (fun (E : EF × Nat × List Nat) => (fun (mul : Nat → Nat → Nat) =>
      (fun (invs : List Nat) => allL (sliceK invs lo len) (branchF mul invs zi d))
      (filterN E.1.cnt fun i => andB (notB (Nat.beq i 0)) (Nat.beq (mul i i) 0)))
    (mulF W (lenA qp) E))
  (enumT n w ta tb prog qp dd)

end CFSG.KC.LQT.RF

end
