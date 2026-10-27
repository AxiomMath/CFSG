module

public import Certificates.Data.Kernel.LocalQT.Pipe

public section

namespace CFSG.KC.LQT.BW

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP

@[expose] noncomputable def imgsW (w g : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => letLs (imgW w g x) fun y => List.cons y ih) l

@[expose] noncomputable def ptsW (w : Nat) (B G : List Nat) : List Nat :=
  appK B (flatK (List.rec (motive := fun _ => List (List Nat)) []
    (fun g _ ih => List.cons (imgsW w g B) ih) G))

@[expose] noncomputable def takeK (m : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih m => Nat.rec (motive := fun _ => List Nat) [] (fun m' _ => List.cons x (ih m')) m)
    l m

@[expose] noncomputable def dropK (m : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x t ih m => Nat.rec (motive := fun _ => List Nat) (List.cons x t) (fun m' _ => ih m') m)
    l m

@[expose] noncomputable def keyW (w nb : Nat) (T : List Nat) : Nat := codeK w (takeK nb T)

@[expose] noncomputable def eqLW (l m : List Nat) : Bool := CFSG.KC.LQT.L.eqL l m

inductive TT where
  | lf : TT
  | nd : TT → Nat → Nat → List Nat → TT → TT

@[expose] noncomputable def memTT (t : TT) (x : Nat) : Bool :=
  TT.rec (motive := fun _ => Bool) false
    (fun _ k _ _ _ ihl ihr => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ihr ihl (ltK x k)) true (Nat.beq x k)) t

@[expose] noncomputable def idxTT (t : TT) (x : Nat) : Nat :=
  TT.rec (motive := fun _ => Nat) 0
    (fun _ k v _ _ ihl ihr => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) ihr ihl (ltK x k)) v (Nat.beq x k)) t

@[expose] noncomputable def tabTT (t : TT) (x : Nat) : List Nat :=
  TT.rec (motive := fun _ => List Nat) []
    (fun _ k _ T _ ihl ihr => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) ihr ihl (ltK x k)) T (Nat.beq x k)) t

@[expose] noncomputable def insTT (t : TT) (x v : Nat) (T : List Nat) : TT :=
  TT.rec (motive := fun _ => TT) (TT.nd TT.lf x v T TT.lf)
    (fun l k u U r ihl ihr => Bool.rec (motive := fun _ => TT)
      (Bool.rec (motive := fun _ => TT) (TT.nd l k u U ihr) (TT.nd ihl k u U r) (ltK x k))
      (TT.nd l k u U r) (Nat.beq x k)) t

@[expose] noncomputable def isEnt (w nb : Nat) (t : TT) (c : List Nat) : Bool :=
  letB (keyW w nb c) fun key => andB (memTT t key) (eqLW (tabTT t key) c)

structure ES where
  kt : TT
  cnt : Nat
  rev : List (List Nat)
  par : List Nat
  cl : List Nat
  fr : List (List Nat)
  ok : Bool

@[expose] noncomputable def letE (y : Nat) (k : Nat → ES) : ES :=
  Nat.rec (motive := fun _ => ES) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def revOn {α : Type} (l acc : List α) : List α :=
  List.rec (motive := fun _ => List α → List α) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons x acc)) l acc

@[expose] noncomputable def zerosOn (m : Nat) (l : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) l (fun _ ih => List.cons 0 ih) m

@[expose] noncomputable def kidsW (w nb : Nat) (app : Nat → List Nat → List Nat) (G : List Nat)
    (i : Nat) (T : List Nat) (st : ES) : ES :=
  List.rec (motive := fun _ => ES → ES) (fun st => st)
    (fun s _ ih st => (fun (c : List Nat) => letE (keyW w nb c) fun key =>
      ih (Bool.rec (motive := fun _ => ES)
        (letE (Nat.succ st.cnt) fun cnt' =>
          ES.mk (insTT st.kt key st.cnt c) cnt' (List.cons c st.rev) (List.cons i st.par)
            (List.cons st.cnt st.cl) (List.cons c st.fr) st.ok)
        (letE (idxTT st.kt key) fun j =>
          Bool.rec (motive := fun _ => ES)
            (ES.mk st.kt st.cnt st.rev st.par (List.cons j st.cl) st.fr false)
            (ES.mk st.kt st.cnt st.rev st.par (List.cons j st.cl) st.fr st.ok)
            (eqLW (tabTT st.kt key) c))
        (memTT st.kt key))) (app s T)) G st

@[expose] noncomputable def roundW (w nb gi : Nat) (app : Nat → List Nat → List Nat) (G : List Nat)
    (F : List (List Nat)) (i : Nat) (st : ES) : ES :=
  List.rec (motive := fun _ => Nat → ES → ES) (fun _ st => st)
    (fun T _ ih i st => letE (Nat.succ i) fun i' => ih i'
      ((fun (st' : ES) => ES.mk st'.kt st'.cnt st'.rev st'.par (zerosOn gi st'.cl) st'.fr st'.ok)
        (kidsW w nb app G i T st))) F i st

@[expose] noncomputable def enumW (w nb gi : Nat) (app : Nat → List Nat → List Nat)
    (G o : List Nat) (dd : Nat) : ES × Nat × List (List Nat) :=
  Nat.rec (motive := fun _ => ES × Nat × List (List Nat))
    (Prod.mk (ES.mk (insTT TT.lf (keyW w nb o) 0 o) 1 [o] [0] [] [] true) (Prod.mk 0 [o]))
    (fun _ ih => Prod.rec (motive := fun _ => ES × Nat × List (List Nat)) (fun st p =>
      Prod.rec (motive := fun _ => ES × Nat × List (List Nat)) (fun i F =>
        (fun (st' : ES) => Prod.mk (ES.mk st'.kt st'.cnt st'.rev st'.par st'.cl [] st'.ok)
            (Prod.mk st.cnt (revOn st'.fr [])))
          (roundW w nb gi app G F i (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok))) p) ih) dd

@[expose] noncomputable def allLL (L : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def enumOK (k fuel : Nat) (E : ES × Nat × List (List Nat)) : Bool :=
  allBs [List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) E.2.2,
    Nat.ble E.1.cnt fuel, Nat.beq E.1.cnt (Nat.pow 2 k), E.1.ok]

@[expose] noncomputable def comW (nb : Nat) (app : Nat → List Nat → List Nat) (G : List Nat)
    (T : List Nat) : Bool :=
  (fun (T0 : List Nat) => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun g _ ih rest => andB (eqLW (takeK nb rest) (app g T0)) (ih (dropK nb rest)))
    G (dropK nb T)) (takeK nb T)

@[expose] noncomputable def cjW (w z g gi p : Nat) : Nat := imgW w gi (imgW w z (imgW w g p))

@[expose] noncomputable def baseWQ (w : Nat) (B : List Nat) (app : Nat → List Nat → List Nat)
    (G : List Nat) (gl : Nat) (o : List Nat) (z g gi h hi k fuel dd : Nat) : Bool :=
  (fun (E : ES × Nat × List (List Nat)) => allBs [enumOK k fuel E,
    allLL E.1.rev (fun T => impB (comW (lenA B) app G T)
      (orB (eqLW T o) (eqLW T (imgsW w z o)))),
    isEnt w (lenA B) E.1.kt (imgsW w gi (imgsW w z (imgsW w g o))),
    isEnt w (lenA B) E.1.kt (imgsW w hi (imgsW w z (imgsW w h o))),
    anyL B fun b => notB (Nat.beq (cjW w z g gi (cjW w z h hi b)) (cjW w z h hi (cjW w z g gi b)))])
  (enumW w (lenA B) gl app G o dd)

@[expose] noncomputable def fstN (R : List Nat) (qp : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (nodeK R p.1) ih) qp

@[expose] noncomputable def qpW (n w : Nat) (B R : List Nat) (qp : List (Nat × Nat)) : Bool :=
  andB (allA qp fun p => andB (Nat.blt p.1 (lenA R)) (Nat.blt p.2 (lenA R)))
  (andB (allA qp fun p => Nat.beq (mulW n w (nodeK R p.2) (nodeK R p.1)) (oneW n w))
    (allL B fun b => Nat.blt b n))

@[expose] noncomputable def baseWR (n w : Nat) (B R : List Nat) (qp : List (Nat × Nat))
    (zn gn gin hn hin k fuel dd : Nat) : Bool :=
  andB (qpW n w B R qp)
  (andB (allBs [Nat.blt zn (lenA R), Nat.blt gn (lenA R), Nat.blt gin (lenA R),
     Nat.blt hn (lenA R), Nat.blt hin (lenA R)])
  (andB (Nat.beq (mulW n w (nodeK R gin) (nodeK R gn)) (oneW n w))
  (andB (Nat.beq (mulW n w (nodeK R hin) (nodeK R hn)) (oneW n w))
  (baseWQ w B (imgsW w) (fstN R qp) (lenA qp) (ptsW w B (fstN R qp)) (nodeK R zn) (nodeK R gn)
    (nodeK R gin) (nodeK R hn) (nodeK R hin) k fuel dd))))

@[expose] noncomputable def baseWK (n w : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (zn gn gin hn hin k fuel dd : Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    (baseWR n w B (slpW n w (codeK w ta) (codeK w tb) prog) qp zn gn gin hn hin k fuel dd)))

end CFSG.KC.LQT.BW

end
