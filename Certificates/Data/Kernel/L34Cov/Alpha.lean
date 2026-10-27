module

public import Certificates.Data.Kernel.L34Cov.Walk
public import Certificates.Data.Kernel.L34Cov.Codes

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Certificates.CosetEnumeration in
@[expose] noncomputable def FW : List (List Nat) :=
  (([commWords (coverPairs 0), commWords (coverPairs 1)] ++ rels ++ [bFive, zOne, zTwo, zThree]).map
    (List.map letterCode))

@[expose] noncomputable def bindB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def eN (j : Nat) (w : List Nat) : Nat :=
  w.foldl (fun s c => Nat.add s (cond (Nat.beq c (Nat.mul 2 j)) 1
    (cond (Nat.beq c (Nat.add (Nat.mul 2 j) 1)) 11 0))) 0 % 12

@[expose] noncomputable def zvC (V : Nat) (TA TB : Nat → Nat) (w : List Nat) : Nat :=
  strictN (Nat.mod (Nat.shiftRight (Mono.walk TB (nat_lit 4) (nat_lit 4) w (nat_lit 0)) 16) 4)
    fun c₂ => Nat.add (Nat.add (Nat.mod (Nat.mul 3 (Nat.add
      (Nat.shiftRight (Mono.walk TA (nat_lit 4) (nat_lit 4) w (nat_lit 0)) 16) (Nat.mul 2 c₂))) 4)
      (Nat.mul 4 c₂)) (Nat.mul 16 (Nat.sub (rwalk V w (nat_lit 1)) 1))

@[expose] noncomputable def zvOK (V : Nat) (TA TB : Nat → Nat) (w : List Nat) (v : Nat) : Bool :=
  cvIdOK V TA TB w (Nat.mod v 4) (Nat.mod (Nat.div v 4) 4) (Nat.div v 16)

@[expose] noncomputable def scalarOK (V : Nat) (w : List Nat) : Bool :=
  bindB (rwalk V w (nat_lit 1)) fun s => rowsOK V w (lamC (Nat.sub s 1))

@[expose] noncomputable def relZ (v vA vB eA eB p : Nat) : Bool :=
  andB (Nat.beq (Nat.mod (Nat.mul p (Nat.add (Nat.add (Nat.mod v 4) (Nat.mul eA (Nat.mod vA 4)))
      (Nat.mul eB (Nat.mod vB 4)))) 4) 0)
    (andB (Nat.beq (Nat.mod (Nat.mul p (Nat.add (Nat.add (Nat.mod (Nat.div v 4) 4)
        (Nat.mul eA (Nat.mod (Nat.div vA 4) 4))) (Nat.mul eB (Nat.mod (Nat.div vB 4) 4)))) 4) 0)
      (Nat.beq (Nat.mod (Nat.mul p (Nat.add (Nat.add (Nat.div v 16) (Nat.mul eA (Nat.div vA 16)))
        (Nat.mul eB (Nat.div vB 16)))) 3) 0))

@[expose] noncomputable def extraOK (V : Nat) (TA TB : Nat → Nat) (F : List (List Nat))
    (U : List (List Nat)) (vA vB k p : Nat) : Bool :=
  bindB (zvC V TA TB (substC U (F.getD k []))) fun v =>
    andB (zvOK V TA TB (substC U (F.getD k [])) v)
      (relZ v vA vB (eN 0 (F.getD k [])) (eN 1 (F.getD k [])) p)

@[expose] noncomputable def alphaOK (V : Nat) (TA TB : Nat → Nat) (F : List (List Nat))
    (uA uB : List Nat) : Bool :=
  bindB (zvC V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 []))) fun vA =>
  bindB (zvC V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 []))) fun vB =>
    andB (zvOK V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 [])) vA)
    (andB (zvOK V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 [])) vB)
    (andB (Mono.allR (nat_lit 2) (nat_lit 7) fun k => scalarOK V (substC [uA, uB] (F.getD k [])))
    (andB (extraOK V TA TB F [uA, uB] vA vB 9 1)
    (andB (extraOK V TA TB F [uA, uB] vA vB 10 4)
    (andB (extraOK V TA TB F [uA, uB] vA vB 11 4) (extraOK V TA TB F [uA, uB] vA vB 12 3))))))

end CFSG.KC.L34Cov

end
