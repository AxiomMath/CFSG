module

public import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuCodeInvInputs

public section

namespace CFSG.Quasithin.H.Mathieu

@[expose] def actC23s2 (p : T23s2.Elem) (m : ℕ) : ℕ := actM (matsC23[p.idx]!) m

@[expose] def predC23 (k : ℕ) (l : List T23s2.Elem) : Bool :=
  let d := Nat.log 2 (fixMasks 11 actC23s2 l).length
  decide (k ≤ 4) && decide (k + 2 ≤ 11 - d) && (k != 4 || xiCheck 11 10 actC23s2 l)

@[expose] def oddC23OK (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) : Prop :=
  ∀ p : T.Elem, p ≠ 1 → (fixMasks 11 (fun q m => actM (mats[q.idx]!) m) [p]).length ≤ 2 ^ 5

@[expose] def matsC23s3 : Array (List ℕ) := matsOfC11 T23s3

@[expose] def matsC23s5 : Array (List ℕ) := matsOfC11 T23s5

@[expose] def matsC23s7 : Array (List ℕ) := matsOfC11 T23s7

@[expose] def matsC23s11 : Array (List ℕ) := matsOfC11 T23s11

@[expose] def matsC23s23 : Array (List ℕ) := matsOfC11 T23s23

end CFSG.Quasithin.H.Mathieu
