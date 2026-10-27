module

public import Certificates.Data.Kernel.He7222.Cls

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow

@[expose] noncomputable def nvLK (w m : Nat) (ss : List Nat) (ks kts : Nat) (T TI : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => strictB (keyF w (cjEv w m (List.cons t List.nil) ss
        (List.cons (getS TI j) List.nil)) (nat_lit 5)) (fun k =>
      bAnd(bIf(Nat.beq k ks, true, Nat.beq k kts), strictB (Nat.succ j) ih)))
    T (nat_lit 0)

end CFSG.KC.HeChain

end
