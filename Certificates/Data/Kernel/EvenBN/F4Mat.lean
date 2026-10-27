module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.KC.F4Mat

open CFSG.KC.Enum CFSG.Fischer

@[expose] noncomputable def ent (N k : Nat) : Nat := Nat.mod (Nat.div N (Nat.pow 4 k)) 4

@[expose] noncomputable def encF (f : Nat → Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih s => Nat.add (f s) (Nat.mul 4 (ih (Nat.succ s)))) n

@[expose] def code (x : F4) : Nat := x.code.val

@[expose] noncomputable def enc (M : Matrix (Fin 5) (Fin 5) F4) : Nat :=
  encF (fun t => code (M ⟨Nat.mod (Nat.div t 5) 5, Nat.mod_lt _ (by decide)⟩
    ⟨Nat.mod t 5, Nat.mod_lt _ (by decide)⟩)) 25 0

@[expose] noncomputable def MT : Nat := 2625168384

@[expose] noncomputable def BT : Nat := 180

@[expose] noncomputable def mt (A B i j k : Nat) : Nat :=
  ent MT (Nat.add (Nat.mul 4 (ent A (Nat.add (Nat.mul 5 i) k))) (ent B (Nat.add (Nat.mul 5 k) j)))

@[expose] noncomputable def dotK (A B i j : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (mt A B i j 0) (mt A B i j 1)) (mt A B i j 2)) (mt A B i j 3))
    (mt A B i j 4)

@[expose] noncomputable def mulK (A B : Nat) : Nat :=
  strictN A fun a => strictN B fun b =>
    encF (fun t => dotK a b (Nat.div t 5) (Nat.mod t 5)) 25 0

@[expose] noncomputable def invK (A : Nat) : Nat :=
  strictN A fun a => encF (fun t => ent BT (ent a (Nat.add (Nat.mul 5 (Nat.sub 4 (Nat.mod t 5)))
    (Nat.sub 4 (Nat.div t 5))))) 25 0

@[expose] noncomputable def chkL (N : Nat) (L : List (Nat × Nat)) : Bool :=
  strictB N fun n => List.rec (motive := fun _ => Bool) true
    (fun p _ ih => Prod.rec (motive := fun _ => Bool)
      (fun k v => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (ent n k) v)) p) L

@[expose] def fShapeL : List (Nat × Nat) :=
  [(1, 0), (2, 0), (3, 0), (4, 0), (7, 0), (8, 0), (9, 0), (13, 0), (14, 0), (19, 0),
   (0, 1), (6, 1), (12, 1), (18, 1), (24, 1), (11, 0), (5, 0), (10, 0)]

end CFSG.KC.F4Mat
