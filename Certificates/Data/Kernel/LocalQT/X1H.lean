module

public import Certificates.Data.Kernel.LocalQT.FusionS

public section

namespace CFSG.KC.LQT.XH

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS

@[expose] noncomputable def bfsCI (n w W g N : Nat) (G : List Nat) (RC SR IS PT CT : Nat → Nat)
    (i : Nat) : Bool :=
  allBs [Nat.blt (SR i) N, Nat.beq (IS (SR i)) i,
    impB (Nat.blt (Nat.succ i) N) (Nat.blt (RC (IS i)) (RC (IS (Nat.succ i)))),
    impB (Nat.beq i 0) (Nat.beq (RC 0) (oneW n w)),
    allL (rangeK g) (fun t => (fun (k : Nat) => allBs [Nat.blt k N,
        Nat.beq (mulW n w (getK G t) (RC i)) (RC k),
        orB (Nat.beq k 0) (Nat.ble (discK W g PT CT k) (Nat.add (Nat.mul i g) t))])
      (fieldT W CT (Nat.add (Nat.mul i (Nat.add g g)) t))),
    orB (Nat.beq i 0) ((fun (p : Nat) => allBs [Nat.blt p i, Nat.blt (discT W g CT p i) g,
        impB (Nat.blt (Nat.succ i) N) (Nat.blt (discK W g PT CT i) (discK W g PT CT (Nat.succ i)))])
      (fieldT W PT i))]

@[expose] noncomputable def x1HB (n w W g N : Nat) (G : List Nat) (RC SR IS PT CT : Nat → Nat)
    (lo len : Nat) : Bool :=
  allR lo len fun i => impB (Nat.blt i N) (bfsCI n w W g N G RC SR IS PT CT i)

@[expose] noncomputable def zPass (mul : Nat → Nat → Nat) (gs Z : List Nat) (x : Nat) : Bool :=
  allL gs fun s => anyL Z fun z => Nat.beq (mul x s) (mul z (mul s x))

@[expose] noncomputable def cPass (mul : Nat → Nat → Nat) (Z : List Nat) (x : Nat) : Bool :=
  allL Z fun y => Nat.beq (mul x y) (mul y x)

@[expose] noncomputable def eqBH (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def incL (N : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => andB (andB (Nat.ble lo x) (Nat.blt x N)) (ih (Nat.succ x))) l 0

@[expose] noncomputable def x1HS (W g N : Nat) (PT CT : Nat → Nat) (Z1L Z2L Z3L QcL : List Nat)
    (lo len : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) (gs : List Nat) => allR lo len fun x => impB (Nat.blt x N) (allBs [
      eqBH (zPass mul gs [0] x) (hasW Z1L x), eqBH (zPass mul gs Z1L x) (hasW Z2L x),
      eqBH (zPass mul gs Z2L x) (hasW Z3L x), eqBH (cPass mul Z3L x) (hasW QcL x)]))
    (mulT W g N PT CT) (mapW (fieldT W CT) (rangeK g))

@[expose] noncomputable def conjK (n w g gi q : Nat) : Nat := mulW n w g (mulW n w q gi)

@[expose] noncomputable def normK (n w : Nat) (L : List Nat) (g gi : Nat) : Bool :=
  andB (allL L fun q => hasW L (conjK n w g gi q)) (allL L fun q => hasW L (conjK n w gi g q))

@[expose] noncomputable def notNormK (n w : Nat) (L : List Nat) (g gi : Nat) : Bool :=
  anyL L fun q => notB (hasW L (conjK n w g gi q))

@[expose] noncomputable def x1HR (n w : Nat) (R : List Nat) (qp : List (Nat × Nat))
    (gn gin hn hin k fuel N : Nat) (GL Z1L Z2L Z3L QcL : List Nat) (GC GIC HC HIC : Nat) : Bool :=
  allBs [qpW n w [] R qp, eqLW GL (fstN R qp),
    Nat.blt gn (lenA R), Nat.blt gin (lenA R), Nat.blt hn (lenA R), Nat.blt hin (lenA R),
    Nat.beq GC (nodeK R gn), Nat.beq GIC (nodeK R gin), Nat.beq HC (nodeK R hn),
    Nat.beq HIC (nodeK R hin),
    Nat.beq (mulW n w GC GIC) (oneW n w), Nat.beq (mulW n w GIC GC) (oneW n w),
    Nat.beq (mulW n w HC HIC) (oneW n w), Nat.beq (mulW n w HIC HC) (oneW n w),
    Nat.beq N (Nat.pow 2 k), Nat.ble N fuel,
    incL N Z1L, incL N Z2L, incL N Z3L, incL N QcL]

@[expose] noncomputable def x1HH (n w : Nat) (ta tb : List Nat) (prog qp : List (Nat × Nat))
    (gn gin hn hin k fuel N : Nat) (GL Z1L Z2L Z3L QcL : List Nat) (GC GIC HC HIC : Nat) : Bool :=
  allBs [tabL n ta, tabL n tb, slpOKK prog 2,
    x1HR n w (slpW n w (codeK w ta) (codeK w tb) prog) qp gn gin hn hin k fuel N GL Z1L Z2L Z3L
      QcL GC GIC HC HIC]

@[expose] noncomputable def x1HN (n w : Nat) (RC : Nat → Nat) (Z1L QcL : List Nat)
    (GC GIC HC HIC : Nat) : Bool :=
  (fun (Z1 Qc : List Nat) => allBs [normK n w Z1 GC GIC, normK n w Qc HC HIC,
      notNormK n w Qc GC GIC, notNormK n w Z1 HC HIC])
    (mapW RC Z1L) (mapW RC QcL)

@[expose] noncomputable def x1HW (n w : Nat) (wprog : List (Nat × Nat)) (GC HC an bn : Nat)
    (ta tb : List Nat) : Bool :=
  andB (slpOKK wprog 2) ((fun (R : List Nat) => allBs [Nat.blt an (lenA R), Nat.blt bn (lenA R),
      Nat.beq (nodeK R an) (codeK w ta), Nat.beq (nodeK R bn) (codeK w tb)])
    (slpW n w GC HC wprog))

end CFSG.KC.LQT.XH

end
