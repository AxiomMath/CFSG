module

public import CFSG.Sporadic.Schreier.Co1WeightStabPerfect
public import CFSG.Sporadic.Schreier.Co1OrbData
public meta import CFSG.Sporadic.Schreier.Co1OrbData
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

@[expose] def conjVec (i : Fin 3) (j : Fin 6) : Fin 6 → ZMod 3 :=
  Native.expVec ((Data.conjExps.getD i.val []).getD j.val [])

@[expose] def actT (i : Fin 3) (f : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  let l := List.ofFn fun j => f ⬝ᵥ conjVec i j
  fun j => l.getD j.val 0

@[expose] def decodeF (n : ℕ) : Fin 6 → ZMod 3 := fun j => ((n / 3 ^ j.val % 3 : ℕ) : ZMod 3)

@[expose] def encodeF (f : Fin 6 → ZMod 3) : ℕ := ∑ j : Fin 6, (f j).val * 3 ^ j.val

@[expose] def orbRep : Fin 4 → Fin 6 → ZMod 3 := ![0, γ 0, Pi.single 5 1, Pi.single 4 1]

@[expose] def orbSize : Fin 4 → ℕ := ![1, 24, 264, 440]

@[expose] def orbTree : Fin 4 → List (ℕ × ℕ × ℕ) :=
  ![Data.orbTree0, Data.orbTree1, Data.orbTree2, Data.orbTree3]

@[expose] def treeCodes (k : Fin 4) : List ℕ := (orbTree k).map (·.1)

@[expose] def treeOK (k : Fin 4) : Bool :=
  (orbTree k).length == orbSize k && ((treeCodes k).map decodeF).Nodup &&
    (treeCodes k).headD 0 == encodeF (orbRep k) &&
    (List.range (orbTree k).length).all fun m => m == 0 ||
      (decide (((orbTree k).getD m (0, 0, 0)).2.1 < m) &&
        decide (((orbTree k).getD m (0, 0, 0)).2.2 < 3) &&
        ((orbTree k).getD m (0, 0, 0)).1 == encodeF (actT (Fin.ofNat 3
          ((orbTree k).getD m (0, 0, 0)).2.2)
          (decodeF ((orbTree k).getD ((orbTree k).getD m (0, 0, 0)).2.1 (0, 0, 0)).1)))

@[expose] def treeClosed (k : Fin 4) : Bool :=
  (treeCodes k).all fun c => (List.finRange 3).all fun i =>
    (treeCodes k).contains (encodeF (actT i (decodeF c)))

end CFSG.Sporadic.Co1Schreier
