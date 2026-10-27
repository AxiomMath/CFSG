module

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import Certificates.Certificate7071

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

theorem T23s2_ok :
    T23s2.check = true ∧ T23s2.n = 128 ∧ T23s2.allOK okM23 = true :=
  Certificates.certificate7071.1

theorem T23s3_ok :
    T23s3.check = true ∧ T23s3.n = 9 ∧ T23s3.allOK okM23 = true :=
  Certificates.certificate7071.2.1

theorem T23s5_ok :
    T23s5.check = true ∧ T23s5.n = 5 ∧ T23s5.allOK okM23 = true :=
  Certificates.certificate7071.2.2.1

theorem T23s7_ok :
    T23s7.check = true ∧ T23s7.n = 7 ∧ T23s7.allOK okM23 = true :=
  Certificates.certificate7071.2.2.2.1

theorem T23s11_ok :
    T23s11.check = true ∧ T23s11.n = 11 ∧ T23s11.allOK okM23 = true :=
  Certificates.certificate7071.2.2.2.2.1

theorem T23s23_ok :
    T23s23.check = true ∧ T23s23.n = 23 ∧ T23s23.allOK okM23 = true :=
  Certificates.certificate7071.2.2.2.2.2

instance : Fact (T23s2.check = true) := ⟨T23s2_ok.1⟩
instance : Fact (T23s3.check = true) := ⟨T23s3_ok.1⟩
instance : Fact (T23s5.check = true) := ⟨T23s5_ok.1⟩
instance : Fact (T23s7.check = true) := ⟨T23s7_ok.1⟩
instance : Fact (T23s11.check = true) := ⟨T23s11_ok.1⟩
instance : Fact (T23s23.check = true) := ⟨T23s23_ok.1⟩

@[expose] def mats23s2 : Array (List ℕ) := matsOf11 T23s2

@[expose] def act23s2 (p : T23s2.Elem) (m : ℕ) : ℕ := actM (mats23s2[p.idx]!) m

@[expose] def inv23s2 : List T23s2.Elem := T23s2.invols

@[expose] def posArr23s2 : Array ℕ := T23s2.posArr inv23s2

@[expose] def pos23s2 (x : T23s2.Elem) : ℕ := posArr23s2[x.idx]!

theorem pos23s2_eq (x : T23s2.Elem) :
    pos23s2 x = pos inv23s2 x := T23s2.posArr_spec _ x

@[expose] def pred23 (k : ℕ) (l : List T23s2.Elem) : Bool :=
  let F := fixMasks 11 act23s2 l
  let d := Nat.log 2 F.length
  decide (k ≤ 4) && (!decide (11 - d ≤ k + 1) || o2OK o2Masks23 F) &&
    (k != 1 || decide (11 - d = 4))

@[expose] def odd23OK (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) : Prop :=
  ∀ p : T.Elem, p ≠ 1 → o2OK o2Masks23 (fixMasks 11 (fun q m => actM (mats[q.idx]!) m) [p]) = true

@[expose] def mats23s3 : Array (List ℕ) := matsOf11 T23s3
@[expose] def mats23s5 : Array (List ℕ) := matsOf11 T23s5
@[expose] def mats23s7 : Array (List ℕ) := matsOf11 T23s7
@[expose] def mats23s11 : Array (List ℕ) := matsOf11 T23s11
@[expose] def mats23s23 : Array (List ℕ) := matsOf11 T23s23

end CFSG.Quasithin.H.Mathieu
