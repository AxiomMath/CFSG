module

public import Certificates.Data.Kernel.KDense.Keys

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def res15I (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => Nat.mod n (nat_lit 15))
    (fun n => Nat.mod (Nat.sub (nat_lit 15) (Nat.mod (Nat.succ n) (nat_lit 15))) (nat_lit 15)) z

@[expose] noncomputable def lgetI (l : List Int) (k : Nat) : Int :=
  List.rec (motive := fun _ => Nat → Int) (fun _ => (0 : Int))
    (fun x _ ih k' => Nat.rec (motive := fun _ => Int) x (fun j _ => ih j) k') l k

@[expose] noncomputable def aIdxT (i j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    ((fun lo hi => Nat.add (nat_lit 24) (Nat.add (Nat.div (Nat.mul lo (Nat.sub (nat_lit 47) lo)) (nat_lit 2))
        (Nat.sub (Nat.sub hi lo) (nat_lit 1))))
      (Bool.rec (motive := fun _ => Nat) j i (Nat.blt i j)) (Bool.rec (motive := fun _ => Nat) i j (Nat.blt i j)))
    i (Nat.beq i j)

@[expose] noncomputable def aPlanes (tab : List Int) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.rec (motive := fun _ => Nat) acc
      (fun j acc2 => (fun r p => Nat.lor acc2 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun b acc3 => Nat.lor acc3 (Nat.shiftLeft (bitN r b) (Nat.add p (Nat.mul b SA)))) (nat_lit 4)))
        (res15I (lgetI tab (aIdxT i j))) (Nat.add (Nat.mul (nat_lit 32) i) j)) (nat_lit 24)) (nat_lit 24)

@[expose] noncomputable def aInitOK (tab : Array Int) (s : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      andB f (andB (Nat.beq X (nat_lit 0)) (andB (Nat.beq W (nat_lit 0))
        (Nat.beq A (Array.rec (motive := fun _ => Nat) (fun l => aPlanes l) tab))))) r2) r) s

@[expose] noncomputable def validX : Nat :=
  Nat.lor (Nat.land (ones (nat_lit 65536)) valW)
    (Nat.lor regOct (Nat.lor (Nat.shiftLeft upA (nat_lit 114688)) (Nat.shiftLeft upA (nat_lit 115712))))

@[expose] noncomputable def xAllOK (s : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      andB f (andB (Nat.beq X validX) (andB (Nat.beq A (nat_lit 0)) (Nat.beq W (nat_lit 0))))) r2) r) s

@[expose] noncomputable def wUnitOK (s : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      andB f (andB (Nat.beq X (nat_lit 0)) (andB (Nat.beq A (nat_lit 0)) (Nat.beq W (nat_lit 1))))) r2) r) s

@[expose] noncomputable def rangeInitOK (lo hi : Nat) (s : St) : Bool :=
  CFSG.KC.orB (andB (Nat.beq lo (nat_lit 300)) (andB (Nat.beq hi (nat_lit 98580)) (xAllOK s)))
    (andB (Nat.beq lo (nat_lit 98580)) (andB (Nat.beq hi (nat_lit 98581)) (wUnitOK s)))

end CFSG.KC.KDense

end
