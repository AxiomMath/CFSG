module

public import Init

public section

namespace CFSG.KC.F4Rank

@[expose] def colR (A c : Nat) : Nat :=
  A >>> (52 * c) % 4503599627370496

@[expose] noncomputable def vappAux (A v : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c ih => (v >>> c % 2 * colR A c) ^^^ ih) n

@[expose] noncomputable def vapp (A v : Nat) : Nat :=
  vappAux A v 52

@[expose] def lowB (x : Nat) : Nat :=
  x &&& (x ^^^ (x - 1)) &&& 4503599627370495

@[expose] def echelon : List Nat → Bool
  | [] => true
  | x :: l => (lowB x != 0 && l.all fun y => y &&& lowB x == 0) && echelon l

@[expose] noncomputable def fixChk (A : Nat) (vs : List Nat) : Bool :=
  vs.all (fun v => vapp A v == v) && echelon vs

@[expose] noncomputable def imgs (A : Nat) (ws : List Nat) : List Nat :=
  ws.map fun w => vapp A w ^^^ w

@[expose] noncomputable def rankChk (A : Nat) (ws : List Nat) : Bool :=
  echelon (imgs A ws)

@[expose] def inMask (M v : Nat) : Bool :=
  v &&& M == v

@[expose] noncomputable def fixSubChk (M A : Nat) (vs : List Nat) : Bool :=
  vs.all (inMask M) && fixChk A vs

@[expose] noncomputable def rankSubChk (M A : Nat) (ws : List Nat) : Bool :=
  ws.all (inMask M) && rankChk A ws

@[expose] noncomputable def stabAux (M A : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c ih => (!M.testBit c || inMask M (colR A c)) && ih) n

@[expose] noncomputable def stabChk (M A : Nat) : Bool :=
  stabAux M A 52

end CFSG.KC.F4Rank

end
