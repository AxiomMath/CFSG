module

public import Init

@[expose] public noncomputable section

namespace Certificates.FzL410.K

def bA (a b : Bool) : Bool := Bool.rec false b a

def bO (a b : Bool) : Bool := Bool.rec b true a

def bI (a b : Bool) : Bool := Bool.rec true b a

def bN (a : Bool) : Bool := Bool.rec true false a

def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => bA (f k) acc) n

def anyR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => bO (f k) acc) n

def cntR (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add (Bool.rec 0 1 (f k)) acc) n

def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ acc => bO (f x) acc) L

def nrm (s : Nat) : Nat :=
  Nat.add (Nat.mod s 4) (Nat.add (Nat.mul 256 (Nat.mod (Nat.div s 256) 4))
    (Nat.add (Nat.mul 65536 (Nat.mod (Nat.div s 65536) 2))
      (Nat.mul 16777216 (Nat.mod (Nat.div s 16777216) 2))))

def evS (g1 g2 g3 g4 x : Nat) : Nat :=
  nrm (Nat.add (Nat.mul g1 (Nat.mod x 256)) (Nat.add (Nat.mul g2 (Nat.mod (Nat.div x 256) 256))
    (Nat.add (Nat.mul g3 (Nat.mod (Nat.div x 65536) 256)) (Nat.mul g4 (Nat.div x 16777216)))))

def cE1 : Nat := 1
def cE2 : Nat := 256
def cR1 : Nat := 65536
def cR2 : Nat := 16777216
def cZ : Nat := 0

def rhoS (x : Nat) : Nat := evS 256 771 16777216 16842752 x
def ttS (x : Nat) : Nat := evS 1 256 65538 16777728 x
def ssS (x : Nat) : Nat := evS 3 768 65536 16777216 x
def llS (x : Nat) : Nat := evS 256 1 16777216 65536 x
def negS (x : Nat) : Nat := evS 3 768 65536 16777216 x
def dblS (x : Nat) : Nat := evS 2 512 0 0 x
def piS (x : Nat) : Nat := evS 0 0 65536 16777216 x

def eqS (c d x : Nat) : Nat := evS c (rhoS c) d (rhoS d) x
def anS (c d x : Nat) : Nat := evS c (rhoS (rhoS c)) d (rhoS (rhoS d)) x

def spr (k : Nat) : Nat :=
  Nat.add (Nat.mod k 4) (Nat.add (Nat.mul 256 (Nat.mod (Nat.div k 4) 4))
    (Nat.add (Nat.mul 65536 (Nat.mod (Nat.div k 16) 2)) (Nat.mul 16777216 (Nat.mod (Nat.div k 32) 2))))

def gen4 (F G : Nat → Nat) : Bool :=
  bA (Nat.beq (F cE1) (G cE1)) (bA (Nat.beq (F cE2) (G cE2))
    (bA (Nat.beq (F cR1) (G cR1)) (Nat.beq (F cR2) (G cR2))))

def injS (c0 d0 : Nat) : Bool :=
  allR 64 (fun k => bI (Nat.beq (eqS c0 d0 (spr k)) cZ) (Nat.beq (spr k) cZ))

def condN (u v : Nat) : Bool :=
  bA (Nat.beq (dblS v) cZ) (bA (bN (Nat.beq (dblS u) cZ)) (bA (bN (Nat.beq (dblS u) (dblS cE1)))
    (bA (bN (Nat.beq (piS v) cZ)) (bN (Nat.beq (piS v) (piS cR1))))))

def injB (u v : Nat) : Bool :=
  allR 64 (fun k => bI (Nat.beq (evS cE1 u cR1 v (spr k)) cZ) (Nat.beq (spr k) cZ))

def normInjB : Bool :=
  allR 64 (fun i => allR 64 (fun j => bI (condN (spr i) (spr j)) (injB (spr i) (spr j))))

def isTN (c d : Nat) : Bool :=
  bA (Nat.beq (dblS d) cZ) (bA (gen4 (fun x => eqS c d (eqS c d x)) (fun x => x))
    (bA (Nat.beq (cntR 64 (fun k => Nat.beq (eqS c d (spr k)) (spr k))) 16)
      (Nat.beq (cntR 64 (fun k => bA (Nat.beq (eqS c d (spr k)) (spr k))
        (Nat.beq (dblS (spr k)) cZ))) 4)))

def psiAN (tgt : Nat → Nat) (c d c0 d0 : Nat) : Bool :=
  bA (Nat.beq (dblS d0) cZ) (bA (gen4 (fun x => eqS c0 d0 (eqS c d x)) (fun x => tgt (eqS c0 d0 x)))
    (bA (gen4 (fun x => eqS c0 d0 (rhoS x)) (fun x => rhoS (eqS c0 d0 x))) (injS c0 d0)))

def rowAN (tgt : Nat → Nat) (c d : Nat) : Bool :=
  bI (isTN c d) (anyR 64 (fun i => anyR 64 (fun j => psiAN tgt c d (spr i) (spr j))))

def stageAT (tgt : Nat → Nat) : Bool :=
  allR 64 (fun i => allR 64 (fun j => rowAN tgt (spr i) (spr j)))

def stageAB : Bool := stageAT ttS

def isSN (c d : Nat) : Bool :=
  bA (Nat.beq (dblS d) cZ) (bA (gen4 (fun x => eqS c d (eqS c d x)) (fun x => x))
    (bA (gen4 (fun x => ttS (eqS c d x)) (fun x => eqS c d (ttS x)))
      (allR 64 (fun k => bI (Nat.beq (ttS (spr k)) (spr k))
        (Nat.beq (eqS c d (spr k)) (negS (spr k)))))))

def isLN (c d l1 l3 : Nat) : Bool :=
  bA (Nat.beq (dblS l3) cZ) (bA (gen4 (fun x => anS l1 l3 (anS l1 l3 x)) (fun x => x))
    (bA (gen4 (fun x => ttS (anS l1 l3 x)) (fun x => anS l1 l3 (ttS x)))
      (gen4 (fun x => eqS c d (anS l1 l3 x)) (fun x => anS l1 l3 (eqS c d x)))))

def psiBN (c d l1 l3 c0 d0 : Nat) : Bool :=
  bA (Nat.beq (dblS d0) cZ) (bA (gen4 (fun x => eqS c0 d0 (anS l1 l3 x)) (fun x => llS (eqS c0 d0 x)))
    (bA (bO (gen4 (fun x => eqS c0 d0 (eqS c d x)) (fun x => ssS (eqS c0 d0 x)))
        (gen4 (fun x => eqS c0 d0 (eqS c d x)) (fun x => ssS (ttS (eqS c0 d0 x)))))
      (bA (gen4 (fun x => eqS c0 d0 (ttS x)) (fun x => ttS (eqS c0 d0 x)))
        (bA (gen4 (fun x => eqS c0 d0 (rhoS x)) (fun x => rhoS (eqS c0 d0 x))) (injS c0 d0)))))

def rowLN (L : List Nat) (c d l1 l3 : Nat) : Bool :=
  bI (isLN c d l1 l3)
    (anyL L (fun P => psiBN c d l1 l3 (Nat.mod P 4294967296) (Nat.div P 4294967296)))

def rowSN (L : List Nat) (c d : Nat) : Bool :=
  bI (isSN c d) (allR 64 (fun a => allR 64 (fun b => rowLN L c d (spr a) (spr b))))

def stageBL (L : List Nat) : Bool :=
  allR 64 (fun i => allR 64 (fun j => rowSN L (spr i) (spr j)))

def psiCodes : List Nat :=
  [72057594037928192, 72059793061183744, 72057602627862784, 72059801651118336, 72057594037928704,
    72059793061184256, 72057602627863296, 72059801651118848, 281474976710657, 283673999966209,
    281483566645249, 283682589900801, 72339069014638849, 72341268037894401, 72339077604573441,
    72341276627828993, 281474976711169, 283673999966721, 281483566645761, 283682589901313,
    72339069014639361, 72341268037894913, 72339077604573953, 72341276627829505, 72057594037928194,
    72059793061183746, 72057602627862786, 72059801651118338, 72057594037928706, 72059793061184258,
    72057602627863298, 72059801651118850, 281474976710659, 283673999966211, 281483566645251,
    283682589900803, 72339069014638851, 72341268037894403, 72339077604573443, 72341276627828995,
    281474976711171, 283673999966723, 281483566645763, 283682589901315, 72339069014639363,
    72341268037894915, 72339077604573955, 72341276627829507]

def stageBB : Bool := stageBL psiCodes

end Certificates.FzL410.K

end
