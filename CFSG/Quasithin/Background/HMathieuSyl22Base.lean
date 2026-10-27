
module

public import Certificates.Certificate7068

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import Certificates.Certificate7068Base

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1


theorem T22s2_ok :
    T22s2.check = true ∧ T22s2.n = 256 ∧ T22s2.allOK okPlus = true :=
  Certificates.certificate7068.1

theorem T22s3_ok :
    T22s3.check = true ∧ T22s3.n = 9 ∧ T22s3.allOK okPlus = true :=
  Certificates.certificate7068.2.1

theorem T22s5_ok :
    T22s5.check = true ∧ T22s5.n = 5 ∧ T22s5.allOK okPlus = true :=
  Certificates.certificate7068.2.2.1

theorem T22s7_ok :
    T22s7.check = true ∧ T22s7.n = 7 ∧ T22s7.allOK okPlus = true :=
  Certificates.certificate7068.2.2.2.1

theorem T22s11_ok :
    T22s11.check = true ∧ T22s11.n = 11 ∧ T22s11.allOK okPlus = true :=
  Certificates.certificate7068.2.2.2.2

instance : Fact (T22s2.check = true) := ⟨T22s2_ok.1⟩
instance : Fact (T22s3.check = true) := ⟨T22s3_ok.1⟩
instance : Fact (T22s5.check = true) := ⟨T22s5_ok.1⟩
instance : Fact (T22s7.check = true) := ⟨T22s7_ok.1⟩
instance : Fact (T22s11.check = true) := ⟨T22s11_ok.1⟩

@[expose] def mats22s2 : Array (List ℕ) := matsOf10 T22s2

@[expose] def act22s2 (p : T22s2.Elem) (m : ℕ) : ℕ := actM (mats22s2[p.idx]!) m

@[expose] def inv22s2 : List T22s2.Elem := T22s2.invols

@[expose] def posArr22s2 : Array ℕ := T22s2.posArr inv22s2

@[expose] def pos22s2 (x : T22s2.Elem) : ℕ := posArr22s2[x.idx]!

theorem pos22s2_eq (x : T22s2.Elem) :
    pos22s2 x = pos inv22s2 x := T22s2.posArr_spec _ x

@[expose] def pred22 (k : ℕ) (l : List T22s2.Elem) : Bool :=
  let F := fixMasks 10 act22s2 l
  let d := Nat.log 2 F.length
  decide (k ≤ 5) && (!decide (10 - d ≤ k + 1) || o2OK o2Masks22 F) &&
    (k != 1 || decide (3 ≤ 10 - d)) && (k != 4 || xiCheck 10 9 act22s2 l) &&
    (k != 5 || (xiCheck 10 10 act22s2 l && pairCheck 10 10 act22s2 l))

@[expose] def odd22OK (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) : Prop :=
  ∀ p : T.Elem, p ≠ 1 → o2OK o2Masks22 (fixMasks 10 (fun q m => actM (mats[q.idx]!) m) [p]) = true

@[expose] def mats22s3 : Array (List ℕ) := matsOf10 T22s3
@[expose] def mats22s5 : Array (List ℕ) := matsOf10 T22s5
@[expose] def mats22s7 : Array (List ℕ) := matsOf10 T22s7
@[expose] def mats22s11 : Array (List ℕ) := matsOf10 T22s11

end CFSG.Quasithin.H.Mathieu
