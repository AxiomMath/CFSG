module

public import Certificates.Data.Kernel.L34W.Outer

public section

namespace CFSG.KC.L34FW

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K CFSG.KC.L34W

@[expose] noncomputable def treeK (T PAR DEP : Nat → Nat) : Bool :=
  bAnd(Nat.beq (DEP (nat_lit 0)) (nat_lit 0),
    allN (nat_lit 315) fun j => bIf(Nat.beq j (nat_lit 0), true,
      strictB (PAR j) fun p =>
        bAnd(bAnd(Nat.blt p (nat_lit 315), Nat.blt (DEP p) (DEP j)),
          commPt (nat_lit 42) (nat_lit 6) (T j) (T p))))

@[expose] noncomputable def genK (T G W : Nat → Nat) : Bool :=
  bAnd(bAnd(bAnd(Nat.blt (W (nat_lit 0)) (nat_lit 315), Nat.blt (W (nat_lit 1)) (nat_lit 315)),
      bAnd(Nat.blt (W (nat_lit 2)) (nat_lit 315), Nat.blt (W (nat_lit 3)) (nat_lit 315))),
    bAnd(Nat.beq (pcomp (nat_lit 42) (nat_lit 6) (mask 6) (T (W (nat_lit 0))) (T (W (nat_lit 1))))
        (G (nat_lit 0)),
      bAnd(Nat.beq (T (W (nat_lit 2))) (G (nat_lit 1)), Nat.beq (T (W (nat_lit 3))) (G (nat_lit 2)))))

end CFSG.KC.L34FW

end
