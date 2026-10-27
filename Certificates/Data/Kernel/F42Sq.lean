module

public import Certificates.Data.Kernel.F42Pc

public section

namespace CFSG.KC.F42

open CFSG.KC.Enum

@[expose] noncomputable def fldW (P w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def stepOK (k A B Q S : Nat) (last : Bool) (c : Nat) : Bool :=
  strictB (Nat.add (fldW A (nat_lit 22) (Nat.shiftRight c (nat_lit 1)))
      (Nat.mul (Nat.land c (nat_lit 1)) (Nat.pow (nat_lit 2) k))) fun q =>
  strictB (mulR q q) fun v =>
  strictB (fldW Q (nat_lit 17) c) fun a =>
  strictB (fldW Q (nat_lit 17) (Nat.succ c)) fun b =>
  bIf(Nat.beq (Nat.mod v (Nat.pow (nat_lit 2) (Nat.succ k))) (nat_lit 0),
    bAnd(Nat.beq b (Nat.succ a), bAnd(Nat.beq (fldW B (nat_lit 22) a) q,
      bIf(last, Nat.beq (fldW S (nat_lit 3) a) (Nat.shiftRight v (nat_lit 22)), true))),
    Nat.beq b a)

@[expose] def wP : Nat := 2117968835592057161715145280975963866001024583741830934604653023721918720332000115025200447593133743567286840023367366699565176716701055633688704

@[expose] def crL : List Nat := [2097152, 524288, 2621440, 786432, 32768, 1081344, 49152, 8192, 532480, 1024,
    2098176, 263168, 33792, 9216, 271360, 512, 2097664, 33280, 1081856, 256, 131328, 8448, 139520, 768, 384, 32, 1048608, 32800,
    1081376, 8224, 4128, 288, 8480, 4384]

@[expose] noncomputable def isRep (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a p, true, ih)) crL

@[expose] noncomputable def conjR (a x : Nat) : Nat := mgR cmK 25 (mulR (2 ^ a) x) a

@[expose] noncomputable def weylR (a x : Nat) : Nat :=
  ((((List.range 24).filter fun k => x.testBit k).map fun k => fldW wP 5 (24 * a + k)) ++
    (if x.testBit 24 then [24] else [])).foldl (fun E k => mgR cmK 25 E k) 0

@[expose] noncomputable def mvR (d x : Nat) : Nat := if d < 4 then conjR d x else weylR (d - 4) x

@[expose] def mvOKR (d x : Nat) : Bool := d < 4 || (d < 8 && !x.testBit (d - 4))

@[expose] noncomputable def rmOK (d : Nat) : Bool :=
  bIf(Nat.blt d (nat_lit 4), true, bIf(Nat.beq d (nat_lit 5), true, Nat.beq d (nat_lit 6)))

@[expose] noncomputable def bfsChk (L S D M Pt n i : Nat) : Bool :=
  strictB (fldW L (nat_lit 22) i) fun p =>
  bIf(bAnd(Nat.beq (fldW S (nat_lit 3) i) (nat_lit 0), bIf(Nat.beq p (nat_lit 0), false, true)),
    bIf(isRep p, Nat.beq (fldW D (nat_lit 8) i) (nat_lit 0),
      strictB (fldW M (nat_lit 3) i) fun m => strictB (fldW Pt (nat_lit 16) i) fun j =>
      bAnd(rmOK m, bAnd(mvOKR m p,
        strictB (Nat.mod (mvR m p) (nat_lit 4194304)) fun y =>
        bAnd(bIf(Nat.beq y (nat_lit 0), false, true), bAnd(Nat.blt j n,
          bAnd(Nat.beq (fldW L (nat_lit 22) j) y,
            Nat.beq (Nat.succ (fldW D (nat_lit 8) j)) (fldW D (nat_lit 8) i))))))),
    true)

end CFSG.KC.F42

end
