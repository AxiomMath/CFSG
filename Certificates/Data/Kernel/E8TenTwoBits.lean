module

public import Certificates.Data.E8TenTwo
public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.E8TenTwoBits

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def comb (B : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih s => Nat.xor (nIf(Nat.beq (Nat.land s 1) 1, b, 0)) (ih (Nat.shiftRight s 1))) B s

@[expose] noncomputable def colCode (F : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun f _ ih => Nat.add (Nat.land (Nat.shiftRight f j) 1) (Nat.mul 2 ih)) F

@[expose] noncomputable def colsOK (F B C : List Nat) : Bool :=
  andB (Nat.beq C.length 20)
    ((List.zip C (List.range 20)).all fun p =>
      Nat.beq (Nat.xor p.1 (Nat.shiftLeft 1 p.2)) (comb B (colCode F p.2)))

@[expose] noncomputable def factOK (G : List (List Nat)) (D : List (List Nat × List Nat × Nat)) : Bool :=
  andB (Nat.beq D.length E8TenTwo.transWords.length)
    ((List.zip E8TenTwo.transWords D).all fun p =>
      andB (Nat.beq p.2.1.length p.2.2.1.length)
        (colsOK p.2.1 p.2.2.1 (E8TenTwo.compCols G p.1)))

@[expose] noncomputable def oBits : Nat :=
  E8TenTwo.bfsTab.foldl (fun a e => Nat.lor a (Nat.shiftLeft 1 e.1)) 0

@[expose] noncomputable def codesIn (O : Nat) (D : List (List Nat × List Nat × Nat)) : Bool :=
  D.all fun d => (List.range (2 ^ d.2.1.length)).all fun s =>
    bIf(Nat.beq (Nat.land (Nat.shiftRight d.2.2 s) 1) 1,
      andB (Nat.blt (comb d.2.1 s) (2 ^ 20))
        (Nat.beq (Nat.land (Nat.shiftRight O (comb d.2.1 s)) 1) 1),
      true)

@[expose] noncomputable def codesOK (D : List (List Nat × List Nat × Nat)) : Bool :=
  Nat.rec (motive := fun _ => Bool) (codesIn 0 D) (fun n _ => codesIn (Nat.succ n) D) oBits

@[expose] noncomputable def flane (k F : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun b acc => nIf(Nat.beq (Nat.land (Nat.shiftRight F b) 1) 1,
      Nat.xor acc (idPlane (Nat.shiftLeft 1 k) b), acc)) k

@[expose] noncomputable def evalT (O : Nat) (Ls : List Nat) (T acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat)
    (fun T acc => nIf(Nat.beq (Nat.land T 1) 1, acc, 0))
    (fun L Ls ih T acc => nIf(Nat.beq T 0, 0,
      (fun h => Nat.lor
          (strictN (Nat.land acc (Nat.xor O L)) (fun a => ih (Nat.mod T h) a))
          (strictN (Nat.land acc L) (fun a => ih (Nat.div T h) a)))
        (Nat.shiftLeft 1 (Nat.shiftLeft 1 Ls.length))))
    Ls T acc

@[expose] noncomputable def lanes (k : Nat) (F : List Nat) : List Nat := (F.map (flane k)).reverse

@[expose] noncomputable def cover (k : Nat) (D : List (List Nat × List Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun d _ ih => strictN (evalT (ones (Nat.shiftLeft 1 k)) (lanes k d.1) d.2.2 (ones (Nat.shiftLeft 1 k)))
      (fun c => Nat.lor c ih)) D

@[expose] noncomputable def coverOK (k : Nat) (D : List (List Nat × List Nat × Nat)) : Bool :=
  Nat.beq (cover k D) (Nat.xor (ones (Nat.shiftLeft 1 k)) 1)

end CFSG.KC.E8TenTwoBits

end
