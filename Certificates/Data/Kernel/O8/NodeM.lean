module

public import Certificates.Data.Kernel.O8.EnumK
public import Batteries.Data.List.Basic

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def swarK : List Nat :=
  (List.range 12).map fun k =>
    orN (Nat.div (nat_lit 4096) (Nat.mul 2 (pw2 k))) fun j =>
      Nat.shiftLeft (maskN (pw2 k)) (Nat.mul (Nat.mul 2 (pw2 k)) j)

@[expose] noncomputable def fixMaskW (SW : List Nat) (y : Nat) : Nat :=
  strictN (maskN (nat_lit 4096)) fun A =>
    Nat.xor A (Nat.land A (orN (nat_lit 12) fun i =>
      (fun r => xorN (nat_lit 12) fun j =>
          nIf(Nat.beq (bitN r j) (nat_lit 1), Nat.xor A (SW.getD j 0), nat_lit 0))
        (Nat.xor (row12 y i) (pw2 i))))

@[expose] noncomputable def popcM (SW : List Nat) (x : Nat) : Nat :=
  (SW.zipIdx.foldl (fun x p => strictN x fun x =>
    Nat.add (Nat.land x p.1) (Nat.land (Nat.shiftRight x (pw2 p.2)) p.1)) x)

@[expose] noncomputable def newGenM (span : List Nat) (y : Nat) : Bool :=
  !(span.contains y) && span.all fun s => decide (y ≤ mul12K y s)

@[expose] noncomputable def commOfK (I : List Nat) (r : Nat) : List Nat :=
  I.filter fun z => z != r && mul12K z r == mul12K r z

@[expose] noncomputable def nodeM (B : Nat) (SW : List Nat) :
    Nat → List Nat → Nat → List Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, span, X, rest =>
    decide (span.length * popcM SW X ≤ B) &&
      rest.tails.all fun
        | [] => true
        | y :: ys => !(newGenM span y) ||
          nodeM B SW fuel (span ++ span.map (mul12K y)) (Nat.land X (fixMaskW SW y))
            (ys.filter fun z => mul12K y z == mul12K z y)

end CFSG.KC.O8

end
