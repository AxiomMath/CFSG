module

public import Certificates.Data.Kernel.Spor.ONPvK

public section

namespace CFSG.KS.ONPl

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.ONPv

@[expose] noncomputable def aT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), iT TT UU (D (nat_lit 79)) x, TT (nat_lit 1) x)

@[expose] noncomputable def aU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), iU TT UU (D (nat_lit 79)) x, UU (nat_lit 1) x)

@[expose] noncomputable def ahT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itT (aT TT UU D) (aU TT UU D) D (nat_lit 77) k x

@[expose] noncomputable def ahU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itU (aT TT UU D) (aU TT UU D) D (nat_lit 77) k x

@[expose] noncomputable def cAt (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (j x : Nat) : Nat :=
  iU TT UU (E j) (iT (hT TT UU D) (hU TT UU D) (E (Nat.add (nat_lit 28) j)) x)

@[expose] noncomputable def ciAt (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (j x : Nat) : Nat :=
  iU (hT TT UU D) (hU TT UU D) (E (Nat.add (nat_lit 28) j)) (iT TT UU (E j) x)

@[expose] noncomputable def eAt (TT UU : Nat → Nat → Nat) (D E : Nat → Nat)
    (YT YU : Nat → Nat → Nat) (v j r p : Nat) : Bool :=
  Nat.beq (ciAt TT UU D E j (iT YT YU v (cAt TT UU D E j p)))
    (iT (qT TT UU D) (qU TT UU D) (E r) p)

@[expose] noncomputable def plLn (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (j p : Nat) : Bool :=
  bAnd(eAt TT UU D E TT UU (D (nat_lit 92)) j (Nat.add (nat_lit 71) (Nat.add j j)) p,
    eAt TT UU D E TT UU (D (Nat.add (nat_lit 93) j)) j (Nat.add (nat_lit 72) (Nat.add j j)) p)

@[expose] noncomputable def plAl (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (j p : Nat) : Bool :=
  bAnd(eAt TT UU D E (ahT TT UU D) (ahU TT UU D) (E (nat_lit 56)) j
      (Nat.add (nat_lit 71) (Nat.add j j)) p,
    eAt TT UU D E (ahT TT UU D) (ahU TT UU D) (E (Nat.add (nat_lit 43) j)) j
      (Nat.add (nat_lit 72) (Nat.add j j)) p)

@[expose] noncomputable def plLnR (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (lo cnt p : Nat) :
    Bool :=
  allBlk lo (fun j => plLn TT UU D E j p) cnt

@[expose] noncomputable def plAlR (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (lo cnt p : Nat) :
    Bool :=
  allBlk lo (fun j => plAl TT UU D E j p) cnt

@[expose] noncomputable def plX (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (p : Nat) : Bool :=
  bAnd(Nat.beq (iT (hT TT UU D) (hU TT UU D) (E (nat_lit 56)) p) (iT TT UU (D (nat_lit 92)) p),
    allBlk (nat_lit 0) (fun k => Nat.beq (iT (hT TT UU D) (hU TT UU D) (E (Nat.add (nat_lit 57) k)) p)
      (iT TT UU (D (Nat.add (nat_lit 107) k)) p)) (nat_lit 14))

@[expose] noncomputable def plP (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) (p : Nat) : Bool :=
  allBlk (nat_lit 0) (fun i =>
    Nat.beq (iT (qT TT UU D) (qU TT UU D) (E (Nat.add (nat_lit 127) (Nat.add i i))) p)
      (iT (qT TT UU D) (qU TT UU D) (E (Nat.add (nat_lit 128) (Nat.add i i))) p)) (nat_lit 7)

@[expose] noncomputable def plHd (TT UU : Nat → Nat → Nat) (D E : Nat → Nat) : Bool :=
  bAnd(strictB (E (nat_lit 141)) fun x => bAnd(Nat.blt x (nat_lit 245520),
      Bool.not (Nat.beq (iT (qT TT UU D) (qU TT UU D) (E (nat_lit 134)) x) x)),
    strictB (E (nat_lit 142)) fun x => bAnd(Nat.blt x (nat_lit 245520),
      Bool.not (Nat.beq (qT TT UU D (nat_lit 2) x) x)))

end CFSG.KS.ONPl

end
