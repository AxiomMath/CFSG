
module

public import Certificates.Certificate7112

public import CFSG.Quasithin.Background.HMathieuPred

@[expose] public section

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Quasithin.H.Mathieu


theorem T12s2_ok :
    T12s2.check = true ∧ T12s2.n = 128 ∧ T12s2.allOK okPair = true :=
  Certificates.certificate7112.1

theorem T12s3_ok :
    T12s3.check = true ∧ T12s3.n = 27 ∧ T12s3.allOK okPair = true :=
  Certificates.certificate7112.2.1

theorem T12s5_ok :
    T12s5.check = true ∧ T12s5.n = 5 ∧ T12s5.allOK okPair = true :=
  Certificates.certificate7112.2.2.1

theorem T12s11_ok :
    T12s11.check = true ∧ T12s11.n = 11 ∧ T12s11.allOK okPair = true :=
  Certificates.certificate7112.2.2.2

instance : Fact (T12s2.check = true) := ⟨T12s2_ok.1⟩
instance : Fact (T12s3.check = true) := ⟨T12s3_ok.1⟩
instance : Fact (T12s5.check = true) := ⟨T12s5_ok.1⟩
instance : Fact (T12s11.check = true) := ⟨T12s11_ok.1⟩

def mats12s2 : Array (List ℕ) := matsOf12 T12s2

def act12s2 (p : T12s2.Elem) (m : ℕ) : ℕ := actM (mats12s2[p.idx]!) m

def inv12s2 : List T12s2.Elem := T12s2.invols

def posArr12s2 : Array ℕ := T12s2.posArr inv12s2

def pos12s2 (x : T12s2.Elem) : ℕ := posArr12s2[x.idx]!

theorem pos12s2_eq (x : T12s2.Elem) :
    pos12s2 x = pos inv12s2 x := T12s2.posArr_spec _ x

def pred12 (k : ℕ) (l : List T12s2.Elem) : Bool :=
  let F := fixMasks 10 act12s2 l
  decide (k ≤ 4) && decide (k + 2 ≤ 10 - Nat.log 2 F.length) &&
    (k != 4 || (decide (F.length ≤ 2 ^ 3) && xiCheck 10 8 act12s2 l))

def odd12OK (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) : Prop :=
  ∀ p : T.Elem, p ≠ 1 → (fixMasks 10 (fun q m => actM (mats[q.idx]!) m) [p]).length ≤ 2 ^ 4

def mats12s3 : Array (List ℕ) := matsOf12 T12s3

def mats12s5 : Array (List ℕ) := matsOf12 T12s5

def mats12s11 : Array (List ℕ) := matsOf12 T12s11

end CFSG.Quasithin.H13.A5.M12
