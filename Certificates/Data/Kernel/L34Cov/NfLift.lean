module

public import Certificates.Data.Kernel.L34Cov.Lift
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.Certificates.CosetEnumeration CFSG.CosetTable

@[expose] def nfStepA {m : Nat} (A : List (Fin 2 × Bool) → List (Fin 2 × Bool))
    (g : Nat → List (Fin 2 × Bool) × Bool) (p : List (Fin 2 × Bool) × Bool) (x : Fin m × Bool) :
    List (Fin 2 × Bool) × Bool :=
  if x.2 then (p.1 ++ (if p.2 then A (g x.1.val).1 else (g x.1.val).1), xor p.2 (g x.1.val).2)
  else (p.1 ++ (if xor p.2 (g x.1.val).2 then A (FreeGroup.invRev (g x.1.val).1)
      else FreeGroup.invRev (g x.1.val).1), xor p.2 (g x.1.val).2)

@[expose] noncomputable def addT (U : List (List (Fin 2 × Bool))) (w : List (Fin 2 × Bool))
    (e : Bool) (c : List (Fin 2 × Bool)) (e' : Bool) (a b : Nat) :
    List (Fin 2 × Bool) × Bool × Nat × Nat :=
  cond e (w ++ substWord U c, e', Nat.add a (eN 0 (c.map letterCode)),
      Nat.add b (eN 1 (c.map letterCode)))
    (w ++ c, e', a, b)

@[expose] noncomputable def nfStepT {m : Nat} (U : List (List (Fin 2 × Bool)))
    (g : Nat → List (Fin 2 × Bool) × Bool) (s : List (Fin 2 × Bool) × Bool × Nat × Nat)
    (x : Fin m × Bool) : List (Fin 2 × Bool) × Bool × Nat × Nat :=
  cond x.2 (addT U s.1 s.2.1 (g x.1.val).1 (xor s.2.1 (g x.1.val).2) s.2.2.1 s.2.2.2)
    (addT U s.1 (xor s.2.1 (g x.1.val).2) (FreeGroup.invRev (g x.1.val).1)
      (xor s.2.1 (g x.1.val).2) s.2.2.1 s.2.2.2)

@[expose] noncomputable def nfT {m : Nat} (U : List (List (Fin 2 × Bool)))
    (g : Nat → List (Fin 2 × Bool) × Bool) (l : List (Fin m × Bool)) :
    List (Fin 2 × Bool) × Bool × Nat × Nat :=
  l.foldl (nfStepT U g) ([], false, 0, 0)

@[expose] noncomputable def nfEntOK (V : Nat) (TA TB : Nat → Nat) (vA vB : Nat)
    (t : List (Fin 2 × Bool) × Bool × Nat × Nat) (s : List (Fin 2 × Bool)) (e : Nat) : Bool :=
  zvOK V TA TB ((t.1 ++ s).map letterCode)
    (corrC e vA vB (Nat.mod t.2.2.1 12) (Nat.mod t.2.2.2 12))

@[expose] noncomputable def nfLiftsOK {m : Nat} (V : Nat) (TA TB : Nat → Nat)
    (F : List (List Nat)) (uA uB : List (Fin 2 × Bool)) (g : Nat → List (Fin 2 × Bool) × Bool)
    (L : List (List (Fin m × Bool) × List (Fin 2 × Bool) × Nat)) : Bool :=
  bindB (zvC V TA TB (invW (uA.map letterCode) ++
      substC [uA.map letterCode, uB.map letterCode] (F.getD 0 []))) fun vA =>
  bindB (zvC V TA TB (invW (uB.map letterCode) ++
      substC [uA.map letterCode, uB.map letterCode] (F.getD 1 []))) fun vB =>
    andB (zvOK V TA TB (invW (uA.map letterCode) ++
      substC [uA.map letterCode, uB.map letterCode] (F.getD 0 [])) vA)
    (andB (zvOK V TA TB (invW (uB.map letterCode) ++
      substC [uA.map letterCode, uB.map letterCode] (F.getD 1 [])) vB)
      (L.all fun x => nfEntOK V TA TB vA vB (nfT [uA, uB] g x.1) x.2.1 x.2.2))

end CFSG.KC.L34Cov

end
