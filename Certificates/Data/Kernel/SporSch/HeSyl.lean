module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def sylF80 (T i : Nat) : Nat :=
  fld(T, Nat.mul (nat_lit 80) i, nat_lit 1208925819614629174706175)

@[expose] noncomputable def sylF5 (T i : Nat) : Nat := fld(T, Nat.mul (nat_lit 5) i, nat_lit 31)

@[expose] noncomputable def sylKey (bs : List Nat) (f : Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.lor (f b) (Nat.shiftLeft ih (nat_lit 14))) bs

@[expose] noncomputable def sylValB (V : Nat → Bool) (m NF CJ : Nat) : Bool :=
  allN m (fun i => bAnd(V (sylF80 NF i), V (sylF80 CJ i)))

@[expose] noncomputable def sylRngB (m MT PAR GEN GI R : Nat) : Bool :=
  bAnd(allN (Nat.mul (nat_lit 3) m) (fun k => Nat.blt (sylF5 MT k) m),
    bAnd(allN m (fun i => bAnd(Nat.blt (sylF5 PAR i) m, Nat.blt (sylF5 GEN i) (nat_lit 3))),
      bAnd(allN (nat_lit 3) (fun j => Nat.blt (sylF5 GI j) m), Nat.blt R m)))

@[expose] noncomputable def sylMulB (P : Nat → Nat → Nat) (bs : List Nat) (m NF MT GI j : Nat) :
    Bool :=
  allN m (fun i => eqOnL bs (P (sylF80 NF (sylF5 MT (Nat.add (Nat.mul m j) i))))
    (fun b => P (sylF80 NF i) (P (sylF80 NF (sylF5 GI j)) b)))

@[expose] noncomputable def sylRootB (P : Nat → Nat → Nat) (bs : List Nat) (NF R : Nat) : Bool :=
  eqOnL bs (P (sylF80 NF R)) (fun b => b)

@[expose] noncomputable def sylKeyB (P : Nat → Nat → Nat) (bs : List Nat) (c NF : Nat) : Bool :=
  allN c (fun i =>
    Nat.blt (sylKey bs (P (sylF80 NF i))) (sylKey bs (P (sylF80 NF (Nat.succ i)))))

@[expose] noncomputable def sylTreeB (m MT PAR GEN DEP R : Nat) : Bool :=
  allN m (fun i => bIf(Nat.beq i R, true,
    bAnd(Nat.blt (sylF5 DEP (sylF5 PAR i)) (sylF5 DEP i),
      Nat.beq (sylF5 MT (Nat.add (Nat.mul m (sylF5 GEN i)) (sylF5 PAR i))) i)))

@[expose] noncomputable def sylConjB (P : Nat → Nat → Nat) (bs : List Nat) (YA YB : Nat → Nat)
    (m NF CJ CL R : Nat) : Bool :=
  allN m (fun i => bIf(Nat.beq i R, true,
    eqOnL bs (fun b => P (sylF80 CJ i) (P (sylF80 NF i) b))
      (fun b => Bool.rec (motive := fun _ => Nat) (YA (P (sylF80 CJ i) b)) (YB (P (sylF80 CJ i) b))
        (Nat.beq (fld(CL, i, nat_lit 1)) (nat_lit 1)))))

end CFSG.KS.SporSch

end
