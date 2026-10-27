module

public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.Misc.M22

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

@[expose] noncomputable def nthL (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def nthW (ws : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) ws i

@[expose] noncomputable def wordAt (n : Nat) (A : Nat → Nat) (nA : Nat) (TW : Nat → List Nat)
    (T : Nat → Nat) (j : Nat) : Bool :=
  andB (lettersK nA (TW j)) (Nat.beq (wordK n A nA (TW j)) (T j))

@[expose] noncomputable def coverAt (n : Nat) (A : Nat → Nat) (nA nT : Nat) (T : Nat → Nat)
    (N : Nat) (E IX : Nat → Nat) (j : Nat) : Bool :=
  allN nA fun a => letB (img (inv n (A a)) j) fun j' => andB (Nat.blt j' nT)
    (letB (IX (Nat.add (Nat.mul j nA) a)) fun t => andB (Nat.blt t N)
      (Nat.beq (E t) (mul n (mul n (T j) (A a)) (inv n (T j')))))

@[expose] noncomputable def q8K (Q : List Nat) (k l : Nat) : Bool :=
  CFSG.KC.LQT.S.memL (Nat.add (Nat.mul 16 k) l) Q

@[expose] noncomputable def noBadK (X Y : Nat) (W : Nat → Nat) (Q : List Nat) (g : Nat) : Bool :=
  letB (mul 22 g X) fun gx => letB (mul 22 g Y) fun gy =>
    allN 9 fun k => impB (Nat.beq gx (mul 22 (W k) g))
      (allN 9 fun l => impB (Nat.beq gy (mul 22 (W l) g)) (q8K Q k l))

end CFSG.KC.Misc.M22

end
