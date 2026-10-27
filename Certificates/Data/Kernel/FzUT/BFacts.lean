module

public import Certificates.Data.Kernel.FzUT.BMod

public section

namespace CFSG.KC.FzBMod

@[expose] noncomputable def letN (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(f x, true, ih)) L

@[expose] noncomputable def memL (v : Nat) (L : List Nat) : Bool := anyL L (fun x => Nat.beq x v)

@[expose] noncomputable def smallB (c : Bool) : Bool :=
  Nat.beq (mulN c 64 64) 128 && Nat.beq (mulN c 64 256) 320 && Nat.beq (mulN c 320 512) 832 &&
  Nat.beq (mulN c 1 128) 129 && Nat.beq (mulN c 128 1) 129 &&
  Nat.beq (mulN c 1 832) 833 && Nat.beq (mulN c 832 1) 833 &&
  Nat.beq (mulN c 128 832) 960 && Nat.beq (mulN c 832 128) 960 &&
  Nat.beq (mulN c 960 1) 961 &&
  Nat.beq (mulN c 1 1) 0 && Nat.beq (mulN c 128 128) 0 && Nat.beq (mulN c 832 832) 0 &&
  Nat.beq (mulN c 4 128) (mulN c 129 4) && Nat.beq (mulN c 2 832) (mulN c 833 2) &&
  Nat.beq (mulN c 64 832) (mulN c 960 64) && Nat.beq (mulN c 66 832) (mulN c 961 66)

@[expose] noncomputable def mMulB : Bool :=
  allN 16 (fun w => allN 16 (fun v =>
    bIf(Nat.beq (w % 2) 0, bIf(Nat.beq (v % 2) 0, Nat.beq (amulL w v % 2) 0, true), true)))

@[expose] noncomputable def mSqB : Bool :=
  allN 16 (fun w => bIf(Nat.beq (w % 2) 0, Nat.beq (amulL w w) 0, true))

@[expose] noncomputable def f3B (c : Bool) (z : Nat) : Bool :=
  Nat.blt 256 (countN 1024 (fun n => Nat.beq (mulN c n z) (mulN c z n)))

@[expose] noncomputable def v2G (c : Bool) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    [0, 4, 8, 12, 32, 36, 40, 44, 64, 68, 72, 76, 96, 100, 104, 108, 16, 20, 24, 28, 48, 52, 56,
      60, 80, 84, 88, 92, 112, 116, 120, 124]
    [0, 4, 8, 12, 16, 20, 26, 30, 64, 68, 72, 76, 80, 84, 90, 94, 32, 36, 40, 44, 48, 52, 56, 60,
      96, 100, 104, 108, 112, 116, 120, 124] c

@[expose] noncomputable def v2BG (c : Bool) (G : List Nat) : Bool :=
  allN 1024 (fun v => bIf(Nat.beq (v / 64 % 2) 0, true, bIf(Nat.beq (mulN c v v) 0,
    anyL G (fun g => bAnd(Nat.blt g 1024, letN (mulN c g v) (fun p =>
      bIf(Nat.beq p (mulN c 320 g), true, Nat.beq p (mulN c 832 g))))), true)))

@[expose] noncomputable def v2B (c : Bool) : Bool := v2BG c (v2G c)

@[expose] noncomputable def w0E (i : Nat) : Nat := nIf(Nat.blt i 4, i, Nat.add i 124)

@[expose] noncomputable def w0N (x : Nat) : Bool :=
  bIf(Nat.blt x 4, true, bAnd(Nat.ble 128 x, Nat.blt x 132))

@[expose] noncomputable def w0B (c : Bool) : Bool :=
  allN 8 (fun i => allN 8 (fun j => w0N (mulN c (w0E i) (w0E j))))

@[expose] noncomputable def e32B (L : List Nat) : Bool :=
  allL L (fun x => bAnd(Nat.blt x 1024, bAnd(Nat.beq (mulN true x x) 0,
    allL L (fun y => letN (mulN true x y) (fun p => bAnd(Nat.beq p (mulN true y x), memL p L))))))

@[expose] noncomputable def e32L1 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 384, 385, 386, 387, 388, 389, 390, 391,
    392, 393, 394, 395, 396, 397, 398, 399]

@[expose] noncomputable def e32L2 : List Nat :=
  [0, 1, 2, 3, 16, 17, 18, 19, 32, 33, 34, 35, 48, 49, 50, 51, 256, 257, 258, 259, 272, 273, 274,
    275, 288, 289, 290, 291, 304, 305, 306, 307]

@[expose] noncomputable def h1BL (L1 L2 : List Nat) : Bool :=
  allN 64 (fun n => bIf(Nat.blt n 4, true, bIf(Nat.beq (mulN true n n) 0,
    bIf(memL n L1, true, memL n L2), true)))

@[expose] noncomputable def h1B : Bool := h1BL e32L1 e32L2

@[expose] noncomputable def v1B : Bool :=
  allN 1024 (fun m => bIf(Nat.beq (m / 64 % 2) 0,
    letN (mulN false m m) (fun s => bIf(Nat.beq (mulN false s s) 0, Nat.blt s 4, true)), true))

end CFSG.KC.FzBMod
