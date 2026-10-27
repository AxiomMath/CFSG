module

public import Certificates.Data.Kernel.FzL410.Codes

@[expose] public noncomputable section

namespace Certificates.FzL410.KM

open Certificates.FzL410.K

def bE (a b : Bool) : Bool := Bool.rec (bN b) b a

def sumR (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add (f k) acc) n

def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ acc => bA (f x) acc) L

def inL (L : List Nat) (v : Nat) : Bool := anyL L (fun x => Nat.beq v x)

def bit (M k : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 k))

def addA (k l : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mod k 4) (Nat.mod l 4)) 4)
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.add (Nat.mod (Nat.div k 4) 4) (Nat.mod (Nat.div l 4) 4)) 4))
      (Nat.add
        (Nat.mul 16 (Nat.mod (Nat.add (Nat.mod (Nat.div k 16) 2) (Nat.mod (Nat.div l 16) 2)) 2))
        (Nat.mul 32 (Nat.mod (Nat.add (Nat.mod (Nat.div k 32) 2) (Nat.mod (Nat.div l 32) 2)) 2))))

def ttA (q : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mod q 4) (Nat.mul 2 (Nat.mod (Nat.div q 16) 2))) 4)
    (Nat.add
      (Nat.mul 4 (Nat.mod (Nat.add (Nat.mod (Nat.div q 4) 4) (Nat.mul 2 (Nat.mod (Nat.div q 32) 2))) 4))
      (Nat.add (Nat.mul 16 (Nat.mod (Nat.div q 16) 2)) (Nat.mul 32 (Nat.mod (Nat.div q 32) 2))))

def ssA (q : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.sub 4 (Nat.mod q 4)) 4)
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.sub 4 (Nat.mod (Nat.div q 4) 4)) 4))
      (Nat.add (Nat.mul 16 (Nat.mod (Nat.div q 16) 2)) (Nat.mul 32 (Nat.mod (Nat.div q 32) 2))))

def llA (q : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.div q 4) 4)
    (Nat.add (Nat.mul 4 (Nat.mod q 4))
      (Nat.add (Nat.mul 16 (Nat.mod (Nat.div q 32) 2)) (Nat.mul 32 (Nat.mod (Nat.div q 16) 2))))

def apA (b : Nat) (f : Nat → Nat) (q : Nat) : Nat := Bool.rec q (f q) (Nat.beq b 1)

def actA (w q : Nat) : Nat :=
  apA (Nat.mod w 2) ttA (apA (Nat.mod (Nat.div w 2) 2) ssA (apA (Nat.mod (Nat.div w 4) 2) llA q))

def addV (v w : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mod v 2) (Nat.mod w 2)) 2)
    (Nat.add (Nat.mul 2 (Nat.mod (Nat.add (Nat.mod (Nat.div v 2) 2) (Nat.mod (Nat.div w 2) 2)) 2))
      (Nat.mul 4 (Nat.mod (Nat.add (Nat.mod (Nat.div v 4) 2) (Nat.mod (Nat.div w 4) 2)) 2)))

def actTab : Nat :=
  5792406967567911201536417853838582764752147854347730857762349756809738116908184367453530341531781852640499642893758811829219435937756844783613146425738243779605249025234947088344246173651578945393412261513012403312667197135233488063240176867198577666002835781237063760486975305426035669851694449299744446437374090397323264504020298560099198816507299495901144109029662833602603852579678696105607788443571911601831451175140786031408307335307835834474659000204230184439719063860838324380918182747540801078268797940606698479836765285307757404525353623451274614054317382657227697344520497100614902577392376657259176345531944637489590567825571644061252186810444607720986849003937719066199264575343806441592242207593754477474186051561083842395638630280411757249043109654814712169909268650854146928111416251554060439187865256036949211102160012982224182818618098485802715793844115733619350158574084769942580870534422061065418427867200

def actT (w q : Nat) : Nat :=
  Nat.land (Nat.shiftRight actTab (Nat.mul 6 (Nat.add (Nat.mul 64 w) q))) 63

def actOK : Bool := allR 8 (fun w => allR 64 (fun q => Nat.beq (actT w q) (actA w q)))

def mulN (m n : Nat) : Nat :=
  Nat.add (addA (Nat.mod m 64) (actT (Nat.div m 64) (Nat.mod n 64)))
    (Nat.mul 64 (addV (Nat.div m 64) (Nat.div n 64)))

def commN (x y : Nat) : Bool := Nat.beq (mulN x y) (mulN y x)

def ordGoN (x : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih r n => Bool.rec (ih (mulN r x) (Nat.succ n)) n (Nat.beq r 0)) f

def ordN (x : Nat) : Nat := ordGoN x 32 x 1

def ordT (O x : Nat) : Nat := Nat.land (Nat.shiftRight O (Nat.mul 4 x)) 15

def ordOK (O : Nat) : Bool := allR 512 (fun x => Nat.beq (ordT O x) (ordN x))

def sqN (s : Nat) : Nat := Nat.mul s s

def cMixN (x y : Nat) : Nat := sqN (Nat.mod (Nat.add x y) 67108859)

def c1N (O N x : Nat) : Nat :=
  Nat.mod (sumR N (fun y => cMixN (Nat.mul (ordT O y) 1000003)
    (Nat.add (Nat.mul (ordT O (mulN x y)) 998244353) 1))) 67108859

def colOK (CI CO : List Nat) (inr : Bool) (c : Nat) : Bool := Bool.rec (inL CO c) (inL CI c) inr

def charS (O N : Nat) (CI CO : List Nat) (pr : Nat → Bool) (lo len : Nat) : Bool :=
  allR len (fun j => colOK CI CO (pr (Nat.add lo j)) (c1N O N (Nat.add lo j)))

def disjB (CI CO : List Nat) : Bool := allL CI (fun c => bN (inL CO c))

def inRN (k : Nat) : Bool := Nat.blt k 256

def inQN (k : Nat) : Bool := Nat.blt k 128

def inPN (k : Nat) : Bool := Nat.blt k 64

def zN (k : Nat) : Bool := bO (Nat.beq k 0) (bO (Nat.beq k 2) (bO (Nat.beq k 8) (Nat.beq k 10)))

def eAN (p : Nat) : Bool := Nat.blt p 16

def fAN (p : Nat) : Bool := Nat.beq (ttA (ssA p)) p

def x2N (p : Nat) : Bool := bA (Nat.beq (Nat.mod p 2) 0) (Nat.beq (Nat.mod (Nat.div p 4) 2) 0)

def sqzB : Bool := allR 512 (fun k => bI (inRN k) (zN (mulN k k)))

def rqC (u w : Nat) : Bool :=
  bA (Nat.beq (Nat.div u 64) (Nat.div w 64))
    (Nat.beq (Nat.div (Nat.mod u 64) 16) (Nat.div (Nat.mod w 64) 16))

def rqS (lo len : Nat) : Bool :=
  allR len (fun j => bI (inRN (Nat.add lo j))
    (allR 512 (fun y => bI (inQN y) (rqC (mulN (Nat.add lo j) y) (mulN y (Nat.add lo j))))))

def qcB : Bool := allR 512 (fun x => bI (inRN x) (bE (allR 16 (fun j => commN x j)) (inQN x)))

def efB : Bool := allR 64 (fun p => bI (eAN p) (bI (fAN p) (zN p)))

def centOfN (w : Nat) (pr : Nat → Bool) : Bool :=
  allR 64 (fun p => bE (Nat.beq (actA w p) p) (pr p))

def centXN (w : Nat) : Bool := allR 64 (fun p => bI (Nat.beq (actA w p) p) (x2N p))

def centPB : Bool :=
  allR 512 (fun i => bI (inRN i) (bI (bN (inPN i))
    (bO (centOfN (Nat.div i 64) eAN) (bO (centOfN (Nat.div i 64) fAN) (centXN (Nat.div i 64))))))

def invFB : Bool :=
  allR 512 (fun i => bI (inRN i) (bI (bN (inPN i)) (bI (Nat.beq (mulN i i) 0)
    (bI (centOfN (Nat.div i 64) fAN) (anyR 16 (fun j => Nat.beq i (mulN j 192)))))))

def cardSB (t n : Nat) : Bool := Nat.beq (cntR 512 (fun k => commN k t)) n

def crN (i x : Nat) : Bool := bA (inRN x) (commN x i)

def zcN (j : Nat) : Nat := Nat.add (Nat.mul 2 (Nat.mod j 2)) (Nat.mul 8 (Nat.div j 2))

def maskOK (i M : Nat) : Bool := allR 512 (fun k => bE (bit M k) (crN i k))

def zcrN (M z : Nat) : Bool := bA (bit M z) (allR 512 (fun c => bI (bit M c) (commN z c)))

def sqPairN (i x y : Nat) : Bool :=
  bA (crN i x) (bA (crN i y) (bA (bN (Nat.beq (mulN x x) 0))
    (bA (bN (Nat.beq (mulN y y) 0)) (bN (Nat.beq (mulN x x) (mulN y y))))))

def clsN (i : Nat) : Bool :=
  allR 512 (fun r => bI (inRN r) (anyR 4 (fun j => Nat.beq (mulN r i) (mulN (mulN i (zcN j)) r))))

def fusB (i M x y : Nat) : Bool :=
  bA (maskOK i M) (bA (Nat.beq (cntR 512 (bit M)) 64) (bA (sqPairN i x y)
    (bA (Nat.beq (cntR 512 (zcrN M)) 8) (clsN i))))

def two256 : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

def invSN (KS a : Nat) : Bool := bA (bit KS a) (bA (Nat.beq (mulN a a) 0) (bN (Nat.beq a 0)))

def maskSOK (KS a K : Nat) : Bool := allR 512 (fun x => bE (bit K x) (bA (bit KS x) (commN x a)))

def slPair (K : Nat) : Bool := bO (Nat.blt K two256) (bN (Nat.beq (cntR 512 (bit K)) 64))

def slPairs (e f : Nat) : Bool :=
  bI (bN (Nat.beq (Nat.mod e 512) (Nat.mod f 512))) (bI (commN (Nat.mod e 512) (Nat.mod f 512))
    (slPair (Nat.land (Nat.div e 512) (Nat.div f 512))))

def slOK (KS : Nat) (D : List Nat) : Bool :=
  bA (allR 512 (fun x => bE (bit KS x) (commN x 64)))
    (bA (allL D (fun e => maskSOK KS (Nat.mod e 512) (Nat.div e 512)))
      (bA (allR 512 (fun a => bI (invSN KS a) (anyL D (fun e => Nat.beq (Nat.mod e 512) a))))
        (allL D (fun e => allL D (fun f => slPairs e f)))))

end Certificates.FzL410.KM

end
