module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.PSearch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  foldN n (fun k s => Nat.add s (f k)) (nat_lit 0)

@[expose] noncomputable def apL (w m : Nat) (ts : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun T _ ih p => strictN (pg w m T p) ih) ts p

@[expose] noncomputable def apI (w m : Nat) (tis : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun T _ ih p => strictN (ih p) (pg w m T)) tis p

@[expose] noncomputable def leafOK (w m nb BP IM : Nat) (ts pr : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun Y _ ih => bAnd(allN nb (fun l =>
      Nat.beq (apL w m ts (pg w m Y (pg w m BP l))) (pg w m Y (pg w m IM l))), ih)) pr

@[expose] noncomputable def child (w : Nat) (TR TRI : Nat → Nat) (f : List Nat → List Nat → Nat → Nat)
    (i o k q IM : Nat) (ts tis : List Nat) : Nat :=
  strictN (TR (Nat.add o k)) (fun T => strictN (TRI (Nat.add o k)) (fun TI =>
    strictN (Nat.lor IM (Nat.shiftLeft q (Nat.mul w i))) (fun IM' => f (T :: ts) (TI :: tis) IM')))

@[expose] noncomputable def pnode (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP nb : Nat)
    (src Ys pr : List Nat) : Nat → Nat → List Nat → List Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Nat)
    (fun _ ts _ IM => nIf(leafOK w m nb BP IM ts pr, nat_lit 1, nat_lit 0))
    (fun _ ih i ts tis IM => strictN (LR i) (fun R => strictN (roff n nw R) (fun o =>
      strictN (nthN src i) (fun s => strictN (nthN Ys i) (fun Y =>
      nIf(Nat.blt s i,
        strictN (pg w m Y (pg w m IM s)) (fun p =>
          strictN (rpos w m nw R (apI w m tis p)) (fun k =>
            nIf(Nat.blt k (rcnt R), child w TR TRI (ih (Nat.succ i)) i o k p IM ts tis,
              nat_lit 0))),
        sumN (rcnt R) (fun k => strictN (apL w m ts (rpt w m R k)) (fun q =>
          nIf(Nat.beq (pg w m Y q) q, child w TR TRI (ih (Nat.succ i)) i o k q IM ts tis,
            nat_lit 0)))))))))

@[expose] noncomputable def pcnt (n w m nw : Nat) (LR TR TRI : Nat → Nat) (BP nb : Nat)
    (src Ys pr : List Nat) : Nat :=
  pnode n w m nw LR TR TRI BP nb src Ys pr nb (nat_lit 0) [] [] (nat_lit 0)

@[expose] noncomputable def srcOK (w m BP nb : Nat) (src Ys : List Nat) : Bool :=
  allN nb fun l => bAnd(Nat.ble (nthN src l) l,
    Nat.beq (pg w m (nthN Ys l) (pg w m BP (nthN src l))) (pg w m BP l))

end CFSG.KS.PSearch

end
