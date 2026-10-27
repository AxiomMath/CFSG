module

public import Certificates.Data.Kernel.Misc.RuInv

public section

namespace CFSG.KC.B45P.RuSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def imgC (TR : Nat → Nat) (o0 o1 c p : Nat) : Nat :=
  apP (TR (Nat.add o0 (Nat.shiftRight c 3))) (apP (TR (Nat.add o1 (Nat.land c 7))) p)

@[expose] noncomputable def decC (R0 R1 : Nat) (TRI : Nat → Nat) (o0 u0 u1 : Nat) : Nat :=
  strictN (rpos 12 4095 48720 R0 u1) (fun a =>
    Nat.add (Nat.mul 8 a) (rpos 12 4095 48720 R1 (apP (TRI (Nat.add o0 a)) u0)))

@[expose] noncomputable def fixC (TR : Nat → Nat) (o0 o1 c : Nat) : Nat :=
  strictN (TR (Nat.add o0 (Nat.shiftRight c 3))) (fun T0 =>
  strictN (TR (Nat.add o1 (Nat.land c 7))) (fun T1 =>
    foldN (nat_lit 4060) (fun x k => nIf(Nat.beq (apP T0 (apP T1 x)) x, Nat.succ k, k))
      (nat_lit 0)))

@[expose] noncomputable def covC (R0 R1 : Nat) (TR TRI CD IX : Nat → Nat) (o0 o1 c : Nat) : Bool :=
  strictB (imgC TR o0 o1 c 0) (fun u0 => strictB (imgC TR o0 o1 c 1) (fun u1 =>
  bAnd(Nat.beq (decC R0 R1 TRI o0 u0 u1) c,
    bIf(bAnd(Nat.blt (IX c) 495, Nat.beq (CD (IX c)) c), true,
    bIf(bAnd(Nat.beq (imgC TR o0 o1 c u0) 0, Nat.beq (imgC TR o0 o1 c u1) 1),
      bIf(bAnd(Nat.beq u0 0, Nat.beq u1 1), true,
        bIf(Nat.beq (fixC TR o0 o1 c) (nat_lit 92), false, true)),
      true)))))

@[expose] noncomputable def invC (TR CD IX K0 K1 : Nat → Nat) (o0 o1 i : Nat) : Bool :=
  strictB (CD i) (fun c =>
  bAnd(Nat.blt c 16384, bAnd(Nat.beq (IX c) i,
  bAnd(Nat.beq (imgC TR o0 o1 c 0) (K0 i), bAnd(Nat.beq (imgC TR o0 o1 c 1) (K1 i),
  bAnd(Nat.beq (imgC TR o0 o1 c (K0 i)) 0, bAnd(Nat.beq (imgC TR o0 o1 c (K1 i)) 1,
    bIf(bAnd(Nat.beq (K0 i) 0, Nat.beq (K1 i) 1), false, true))))))))

@[expose] noncomputable def keyC (K0 K1 : Nat → Nat) (k u0 u1 : Nat) : Bool :=
  bAnd(Nat.ble k 495, bAnd(Nat.beq (K0 k) u0, Nat.beq (K1 k) u1))

@[expose] noncomputable def pairC (TR CD K0 K1 CM PR : Nat → Nat) (o0 o1 i ci j : Nat) : Bool :=
  strictB (CD j) (fun cj =>
  strictB (imgC TR o0 o1 ci (K0 j)) (fun p0 => strictB (imgC TR o0 o1 ci (K1 j)) (fun p1 =>
  strictB (imgC TR o0 o1 cj (K0 i)) (fun q0 => strictB (imgC TR o0 o1 cj (K1 i)) (fun q1 =>
    bIf(bAnd(Nat.beq p0 q0, Nat.beq p1 q1),
      bAnd(Nat.testBit (CM i) j, keyC K0 K1 (fld(PR i, Nat.mul 9 j, 511)) p0 p1),
      bIf(Nat.testBit (CM i) j, false, true)))))))

@[expose] noncomputable def rowC (TR CD K0 K1 CM PR : Nat → Nat) (o0 o1 i : Nat) : Bool :=
  strictB (CD i) (fun ci => allN 495 (fun j => pairC TR CD K0 K1 CM PR o0 o1 i ci j))

@[expose] def cK (CM : Nat → Nat) (i j : Nat) : Bool :=
  if i < 495 ∧ j < 495 then Nat.testBit (CM i) j else true

@[expose] def pK (PR : Nat → Nat) (i j : Nat) : Nat :=
  if i < 495 then (if j < 495 then fld(PR i, Nat.mul 9 j, 511) else i) else j

end CFSG.KC.B45P.RuSyl

end
