module

public section

namespace CFSG.Quasithin.D35Chk

@[expose] def bit (a k : Nat) : Nat := Nat.land (Nat.shiftRight a k) 1

@[expose] def rowOf (a i : Nat) : Nat := Nat.land (Nat.shiftRight a (Nat.mul 5 i)) 31

@[expose] def vecMul (r b : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.mul (bit r 0) (rowOf b 0)) (Nat.mul (bit r 1) (rowOf b 1)))
    (Nat.mul (bit r 2) (rowOf b 2))) (Nat.mul (bit r 3) (rowOf b 3))) (Nat.mul (bit r 4) (rowOf b 4))

@[expose] def bmul (a b : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (vecMul (rowOf a 0) b) (Nat.shiftLeft (vecMul (rowOf a 1) b) 5))
    (Nat.shiftLeft (vecMul (rowOf a 2) b) 10)) (Nat.shiftLeft (vecMul (rowOf a 3) b) 15))
    (Nat.shiftLeft (vecMul (rowOf a 4) b) 20)

@[expose] def bT (a : Nat) : Nat :=
  (List.range 25).foldl
    (fun acc q => Nat.lor acc (Nat.shiftLeft (bit a (Nat.add (Nat.mul 5 (Nat.mod q 5)) (Nat.div q 5))) q)) 0

@[expose] def upos : List Nat := [4, 3, 9, 2, 8, 14, 1, 7, 13, 19]

@[expose] def lpos : List Nat := [20, 15, 21, 10, 16, 22, 5, 11, 17, 23]

@[expose] def idm : Nat := 17043521

@[expose] def unitri (c : Nat) : Nat :=
  (List.range 10).foldl (fun acc p => Nat.lor acc (Nat.shiftLeft (bit c p) (upos.getD p 0))) idm

@[expose] def upE (p : Nat) : Nat := Nat.shiftLeft 1 (upos.getD p 0)

@[expose] def altE (p : Nat) : Nat := Nat.lor (upE p) (Nat.shiftLeft 1 (lpos.getD p 0))

@[expose] def isInv (c : Nat) : Bool :=
  !(Nat.beq c 0) && Nat.beq (bmul (unitri c) (unitri c)) idm

@[expose] def commCol (g p : Nat) : Nat := Nat.xor (bmul (unitri g) (upE p)) (bmul (upE p) (unitri g))

@[expose] def fixCol (g p : Nat) : Nat :=
  Nat.xor (bmul (bmul (unitri g) (altE p)) (bT (unitri g))) (altE p)

@[expose] def fixColD (g p : Nat) : Nat :=
  Nat.xor (bmul (bmul (bT (unitri g)) (altE p)) (unitri g)) (altE p)

@[expose] def packRows (col : Nat → Nat) : List Nat :=
  upos.map fun u =>
    (List.range 10).foldl (fun acc p => Nat.lor acc (Nat.shiftLeft (bit (col p) u) p)) 0

@[expose] def full : Nat := Nat.sub (Nat.pow 2 1024) 1

@[expose] def bitMasks : List Nat :=
  (List.range 10).map fun k =>
    (List.range 1024).foldl (fun m b => Nat.lor m (Nat.shiftLeft (bit b k) b)) 0

@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | m :: ms, r => Nat.xor (Nat.mul (Nat.land r 1) m) (xorSel ms (Nat.shiftRight r 1))

@[expose] def kerMask (rows : List Nat) : Nat :=
  rows.foldl (fun acc r =>
    bif Nat.beq r 0 then acc else Nat.land acc (Nat.xor full (xorSel bitMasks r))) full

@[expose] def pv (S k : Nat) : Nat :=
  bif Nat.beq (Nat.land (Nat.shiftRight S (Nat.pow 2 k)) (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1)) 0 then 0 else 1

@[expose] def pivotDim (S : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pv S 0) (pv S 1)) (pv S 2))
    (pv S 3)) (pv S 4)) (pv S 5)) (pv S 6)) (pv S 7)) (pv S 8)) (pv S 9)

@[expose] def topBit (r : Nat) : Nat :=
  let k0 := bif Nat.beq (Nat.shiftRight r 512) 0 then 0 else 512
  let k1 := Nat.add k0 (bif Nat.beq (Nat.shiftRight r (Nat.add k0 256)) 0 then 0 else 256)
  let k2 := Nat.add k1 (bif Nat.beq (Nat.shiftRight r (Nat.add k1 128)) 0 then 0 else 128)
  let k3 := Nat.add k2 (bif Nat.beq (Nat.shiftRight r (Nat.add k2 64)) 0 then 0 else 64)
  let k4 := Nat.add k3 (bif Nat.beq (Nat.shiftRight r (Nat.add k3 32)) 0 then 0 else 32)
  let k5 := Nat.add k4 (bif Nat.beq (Nat.shiftRight r (Nat.add k4 16)) 0 then 0 else 16)
  let k6 := Nat.add k5 (bif Nat.beq (Nat.shiftRight r (Nat.add k5 8)) 0 then 0 else 8)
  let k7 := Nat.add k6 (bif Nat.beq (Nat.shiftRight r (Nat.add k6 4)) 0 then 0 else 4)
  let k8 := Nat.add k7 (bif Nat.beq (Nat.shiftRight r (Nat.add k7 2)) 0 then 0 else 2)
  Nat.add k8 (bif Nat.beq (Nat.shiftRight r (Nat.add k8 1)) 0 then 0 else 1)

@[expose] def packN (f : Nat → Nat) (w : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => packN f w n (Nat.lor acc (Nat.shiftLeft (f n) (Nat.mul w n)))

@[expose] def look (T w j : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul w j)) (Nat.sub (Nat.pow 2 w) 1)

@[expose] def invMask : Nat := packN (fun c => bif isInv c then 1 else 0) 1 1024 0

@[expose] def cmTab : Nat :=
  packN (fun c => bif isInv c then kerMask (packRows (commCol c)) else 0) 1024 1024 0

@[expose] def fxTab : Nat :=
  packN (fun c => bif isInv c then kerMask (packRows (fixCol c)) else 0) 1024 1024 0

@[expose] def fdTab : Nat :=
  packN (fun c => bif isInv c then kerMask (packRows (fixColD c)) else 0) 1024 1024 0

@[expose] def nbTab : Nat := packN (fun t => Nat.xor full (bitMasks.getD t 0)) 1024 10 0

structure Node where
  m : Nat
  FS : Nat
  FD : Nat
  M : Nat

@[expose] def childOf (nd : Node) (g : Nat) : Node where
  m := Nat.add nd.m 1
  FS := Nat.land nd.FS (look fxTab 1024 g)
  FD := Nat.land nd.FD (look fdTab 1024 g)
  M := Nat.land (Nat.land (Nat.shiftLeft (Nat.shiftRight nd.M (Nat.add g 1)) (Nat.add g 1))
    (look cmTab 1024 g)) (look nbTab 1024 (topBit g))

@[expose] def nodeOK (nd : Node) : Bool :=
  Nat.beq nd.m 0 ||
    !(Nat.ble 10 (Nat.add nd.m (pivotDim nd.FS)) && Nat.ble 10 (Nat.add nd.m (pivotDim nd.FD)))

@[expose] def runAux : Nat → List (Node × Nat) → Bool
  | 0, st => st.isEmpty
  | _ + 1, [] => true
  | f + 1, (nd, rem) :: rest =>
    bif Nat.beq rem 0 then runAux f rest else
      let g := topBit rem
      let ch := childOf nd g
      nodeOK ch && runAux f ((ch, ch.M) :: (nd, Nat.xor rem (Nat.pow 2 g)) :: rest)

@[expose] def root : Node where
  m := 0
  FS := full
  FD := full
  M := invMask

@[expose] def run : Bool := runAux 20000 [(root, root.M)]

end CFSG.Quasithin.D35Chk
