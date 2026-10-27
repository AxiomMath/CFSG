
module

public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public meta import CFSG.Quasithin.Background.HMathieuCodeInvInputs

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

@[expose] def normalChainB {d : ℕ} (T : PT d) [Fact (T.check = true)] (l : List T.Elem) : Bool :=
  let S := subprods l
  (List.finRange T.n).all fun i => l.all fun a =>
    decide (T.elemEquiv.symm i * a * (T.elemEquiv.symm i)⁻¹ ∈ S)

@[expose] def oddFixOK (n b : ℕ) (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) :
    Prop :=
  ∀ p : T.Elem, p ≠ 1 → (fixMasks n (fun q m => actM (mats[q.idx]!) m) [p]).length ≤ 2 ^ b

@[expose] def codeAct24 (p : T24s2.Elem) (m : ℕ) : ℕ := actM (matsC24[p.idx]!) m

@[expose] def codeFixTab24 : Array (List ℕ) :=
  Array.ofFn fun i : Fin T24s2.n =>
    let p := T24s2.elemEquiv.symm i
    if p * p = 1 then fixMasks 11 codeAct24 [p] else []

@[expose] def codeFixMasks24 : List T24s2.Elem → List ℕ
  | [] => fixMasks 11 codeAct24 []
  | a :: l => (codeFixTab24[a.idx]!).filter fun m => l.all fun b => codeAct24 b m == m

@[expose] def predHF24 (l : List T24s2.Elem) : Bool :=
  let k := l.length
  let d := Nat.log 2 (codeFixMasks24 l).length
  (k == 0 || !decide (11 - d ≤ k + 1) || decide (7 ≤ 11 - d)) &&
    (k != 4 || decide (7 ≤ 11 - d)) && (k != 6 || (d % 2 == 0 && normalChainB T24s2 l))

@[expose] def matsC24s3 : Array (List ℕ) := matsOfC11 T24s3

@[expose] def matsC24s5 : Array (List ℕ) := matsOfC11 T24s5

@[expose] def matsC24s7 : Array (List ℕ) := matsOfC11 T24s7

@[expose] def matsC24s11 : Array (List ℕ) := matsOfC11 T24s11

@[expose] def matsC24s23 : Array (List ℕ) := matsOfC11 T24s23

@[expose] def codeAct22 (p : T22s2.Elem) (m : ℕ) : ℕ := actM (matsC22[p.idx]!) m

@[expose] def codeFixTab22 : Array (List ℕ) :=
  Array.ofFn fun i : Fin T22s2.n =>
    let p := T22s2.elemEquiv.symm i
    if p * p = 1 then fixMasks 10 codeAct22 [p] else []

@[expose] def codeFixMasks22 : List T22s2.Elem → List ℕ
  | [] => fixMasks 10 codeAct22 []
  | a :: l => (codeFixTab22[a.idx]!).filter fun m => l.all fun b => codeAct22 b m == m

@[expose] def predHF22 (l : List T22s2.Elem) : Bool :=
  let k := l.length
  let d := Nat.log 2 (codeFixMasks22 l).length
  (k == 0 || !decide (10 - d ≤ k + 1) || decide (6 ≤ 10 - d)) &&
    (k != 5 || normalChainB T22s2 l)

@[expose] def matsC22s3 : Array (List ℕ) := matsOfC10 T22s3

@[expose] def matsC22s5 : Array (List ℕ) := matsOfC10 T22s5

@[expose] def matsC22s7 : Array (List ℕ) := matsOfC10 T22s7

@[expose] def matsC22s11 : Array (List ℕ) := matsOfC10 T22s11

end CFSG.Quasithin.H.Mathieu
