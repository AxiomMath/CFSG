module

public import Certificates.Data.Kernel.LocalQT.PcW

public section

namespace CFSG.KC.LQT.PcOm

open CFSG.KC.Enum CFSG.KC.LQT.PcW

@[expose] noncomputable def insB (a : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons a List.nil)
    (fun b t ih => Bool.rec (motive := fun _ => List Nat) (List.cons b ih)
      (List.cons a (List.cons b t)) (Nat.ble a b)) l

@[expose] noncomputable def srtB (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => insB a ih) l

@[expose] noncomputable def lstEqB (x : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun y => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) y)
    (fun a _ ih y => List.rec (motive := fun _ => Bool) false
      (fun b t _ => bAnd(Nat.beq a b, ih t)) y) x

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => nIf(Nat.beq j 0, x, ih (Nat.sub j 1))) l i

@[expose] noncomputable def omAt (n w m c N : Nat) (lbls : List (List Nat)) (row : List Nat)
    (i : Nat) : Bool :=
  (fun x t => bAnd(Nat.blt t N, bAnd(allL x (fun p => Nat.blt p n),
    lstEqB (srtB (imgsK w m c x)) (nthL lbls t)))) (nthL lbls i) (nthN row i)

@[expose] noncomputable def omK (n w m : Nat) (Lc : Nat → Nat) (nl N : Nat)
    (lbls : List (List Nat)) (pn : List (List Nat)) : Bool :=
  allN nl (fun l => strictB (Lc l) (fun c => allN N (omAt n w m c N lbls (nthL pn l))))

end CFSG.KC.LQT.PcOm

end
