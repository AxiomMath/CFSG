module

public import Certificates.Data.Kernel.S1277KLat

public section

namespace CFSG.KC.S1277Sig

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod

@[expose] noncomputable def apK (t : List ℕ) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0) (fun c _ ih x => c * (x % 2) ^^^ ih (x / 2)) t x

@[expose] def orMask (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun x acc => acc ||| 1 <<< f x) n

@[expose] noncomputable def eqL : List ℕ → List ℕ → Bool :=
  fun l => List.rec (motive := fun _ => List ℕ → Bool)
    (fun l' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l')
    (fun a _ ih l' => List.rec (motive := fun _ => Bool) false (fun b r _ => Nat.beq a b && ih r) l')
    l

@[expose] noncomputable def ckL (d L : ℕ) (b : List ℕ) (k : ℕ) : List ℕ :=
  (List.range (2 ^ d)).filter fun c =>
    allLt (2 ^ k) fun y => !Nat.beq c (apK b y) &&
      (L.testBit (c ^^^ apK b y) == L.testBit (b.getD k 0 ^^^ apK b y))

@[expose] noncomputable def tChk (d L : ℕ) (b : List ℕ) (k : ℕ) (t : List ℕ) : Bool :=
  Nat.beq t.length d && allL t (fun c => Nat.blt c (2 ^ d)) &&
    allLt k (fun i => Nat.beq (apK t (b.getD i 0)) (b.getD i 0)) &&
    Nat.beq (orMask (2 ^ d) (apK t)) (2 ^ 2 ^ d - 1) &&
    allLt (2 ^ d) fun x => L.testBit (apK t x) == L.testBit x

@[expose] noncomputable def lvlChk (d L : ℕ) (b : List ℕ) (k : ℕ) (ts : List (List ℕ)) : Bool :=
  eqL (ckL d L b k) (ts.map fun t => apK t (b.getD k 0)) &&
    allL (List.range ts.length) fun j => tChk d L b k (ts.getD j [])

@[expose] noncomputable def sigChk (d L : ℕ) (b : List ℕ) (T : List (List (List ℕ))) : Bool :=
  Nat.beq b.length d && allL b (fun c => Nat.blt c (2 ^ d)) &&
    Nat.beq (orMask (2 ^ d) (apK b)) (2 ^ 2 ^ d - 1) &&
    allL (List.range d) fun k => lvlChk d L b k (T.getD k [])

@[expose] noncomputable def sigAll (ds ls : List ℕ) (bs : List (List ℕ))
    (Ts : List (List (List (List ℕ)))) : Bool :=
  allL (List.range ds.length) fun j => sigChk (ds.getD j 0) (ls.getD j 0) (bs.getD j []) (Ts.getD j [])

end CFSG.KC.S1277Sig

end
