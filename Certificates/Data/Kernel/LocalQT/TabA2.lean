module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.TabA2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 42) (nat_lit 6) (mask 6) p q

@[expose] noncomputable def idn : Nat := pidn (nat_lit 42) (nat_lit 6)

@[expose] noncomputable def cn (p : Nat) : Bool :=
  canonK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) p

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS (nat_lit 42) (nat_lit 6) (mask 6) p

@[expose] noncomputable def at0 (p : Nat) : Nat := pg (nat_lit 6) (mask 6) p (nat_lit 0)

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def memU (U : Nat → Nat) (x : Nat) : Bool :=
  anyK (nat_lit 16) (fun l => Nat.beq (U l) x)

@[expose] noncomputable def invOK (X XI : Nat) : Bool :=
  bAnd(permOK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) X XI,
    bAnd(cn XI, Nat.beq (pc XI X) idn))

@[expose] noncomputable def u1K (T U W : Nat → Nat) (cnt : Nat) : Bool :=
  allN (nat_lit 16) (fun j => bAnd(cn (U j), bAnd(Nat.blt (W j) cnt,
    bAnd(Nat.beq (T (W j)) (U j), bAnd(Nat.beq (at0 (U j)) (nat_lit 0),
      Nat.beq (pc (U j) (U j)) idn)))))

@[expose] noncomputable def u2K (U : Nat → Nat) : Bool :=
  allN (nat_lit 16) (fun i => allN (nat_lit 16) (fun j => memU U (pc (U i) (U j))))

@[expose] noncomputable def rK (U : Nat → Nat) (R : Nat) : Bool :=
  bAnd(cn R, bAnd(Nat.beq (pc R R) idn,
    allN (nat_lit 16) (fun j => memU U (pc (pc R (U j)) R))))

@[expose] noncomputable def a0K (T U : Nat → Nat) (A R q cnt : Nat) : Bool :=
  bAnd(cn A, bAnd(memU U A, bAnd(bIf(Nat.beq A idn, false, true), bAnd(Nat.blt q cnt,
    bAnd(Nat.beq (T q) A, Nat.beq (pc A R) (pc R A))))))

@[expose] noncomputable def zK (T U : Nat → Nat) (Z R q cnt : Nat) : Bool :=
  bAnd(cn Z, bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) Z, bAnd(Nat.beq (pc Z R) (pc R Z),
    bAnd(Nat.beq (at0 Z) (nat_lit 0), bAnd(Nat.beq (pc (pc Z Z) Z) idn,
    bAnd(bIf(Nat.beq Z idn, false, true),
    allN (nat_lit 16) (fun j => bIf(Nat.beq (pc Z (U j)) (pc (U j) Z), Nat.beq (U j) idn,
      true)))))))))

@[expose] noncomputable def transK (T U W : Nat → Nat) (A cnt : Nat) : Bool :=
  allN (nat_lit 16) (fun j => bIf(Nat.beq (U j) idn, true,
    strictB (W j) (fun k => bAnd(Nat.blt k cnt, strictB (T k) (fun X =>
      bAnd(Nat.beq (at0 X) (nat_lit 0), strictB (pinv X) (fun XI =>
        bAnd(invOK X XI, Nat.beq (pc (pc X A) XI) (U j)))))))))

@[expose] noncomputable def witK (U : Nat → Nat) (R : Nat) : Bool :=
  allN (nat_lit 16) (fun j => bIf(Nat.beq (pc R (U j)) (pc (U j) R),
    anyK (nat_lit 16) (fun i => Nat.beq (pc (pc (pc R (U i)) R) (U i)) (U j)), true))

@[expose] noncomputable def puK (T U : Nat → Nat) (k : Nat) : Bool :=
  strictB (T k) (fun X => bIf(Nat.beq (at0 X) (nat_lit 0), strictB (pinv X) (fun XI =>
    bAnd(invOK X XI, allN (nat_lit 16) (fun j => memU U (pc (pc X (U j)) XI)))), true))

@[expose] noncomputable def redK (T U V : Nat → Nat) (R cnt k : Nat) : Bool :=
  strictB (T k) (fun X => bIf(bAnd(Nat.beq (pc X R) (pc R X), Nat.beq (pc X X) idn),
    strictB (V k) (fun y => bAnd(Nat.blt y cnt, strictB (T y) (fun Y =>
      bAnd(Nat.beq (pc Y R) (pc R Y), strictB (pinv Y) (fun YI =>
        bAnd(invOK Y YI, memU U (pc (pc Y X) YI))))))), true))

@[expose] noncomputable def sK (G T PL POS SRT SRI U V : Nat → Nat) (R cnt lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i cnt,
    bAnd(penumPtK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) false G G (nat_lit 3) cnt
      T PL POS SRT SRI i, bAnd(puK T U i, redK T U V R cnt i)), true)))

end CFSG.KS.TabA2

end
