module

public import Certificates.Data.Kernel.Cert690.Base

public section

namespace CFSG.KC.C690

@[expose] noncomputable def bitK (m p : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m p) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def passL (W : IT) (n M : Nat) (ks : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ m => Nat.beq m M)
    (fun p _ ih j m => bAnd(Nat.blt p n,
      bIf(bitK m p, ih (Nat.succ j) m,
        bAnd(Nat.beq (W.find p n) j,
          ih (Nat.succ j) (Nat.lor m (Nat.shiftLeft (nat_lit 1) p)))))) ks

@[expose] noncomputable def passGo (T W : IT) (n M r : Nat) (E inv : List Nat) : Bool :=
  bAnd(Nat.beq E.length inv.length,
    passL W n M (List.zipWith (fun x y => T.find (mulF (mulF x r) y) n) E inv) (nat_lit 0)
      (nat_lit 0))

end CFSG.KC.C690

end
