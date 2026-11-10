
module

public import Certificates.Certificate7074

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuAvoid
public meta import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import Certificates.Certificate7074Base

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1


theorem T24s2_ok :
    T24s2.check = true ∧ T24s2.n = 1024 ∧ T24s2.allOK okAut = true :=
  Certificates.certificate7074.1

theorem T24s3_ok :
    T24s3.check = true ∧ T24s3.n = 27 ∧ T24s3.allOK okAut = true :=
  Certificates.certificate7074.2.1

theorem T24s5_ok :
    T24s5.check = true ∧ T24s5.n = 5 ∧ T24s5.allOK okAut = true :=
  Certificates.certificate7074.2.2.1

theorem T24s7_ok :
    T24s7.check = true ∧ T24s7.n = 7 ∧ T24s7.allOK okAut = true :=
  Certificates.certificate7074.2.2.2.1

theorem T24s11_ok :
    T24s11.check = true ∧ T24s11.n = 11 ∧ T24s11.allOK okAut = true :=
  Certificates.certificate7074.2.2.2.2.1

theorem T24s23_ok :
    T24s23.check = true ∧ T24s23.n = 23 ∧ T24s23.allOK okAut = true :=
  Certificates.certificate7074.2.2.2.2.2

instance : Fact (T24s2.check = true) := ⟨T24s2_ok.1⟩
instance : Fact (T24s3.check = true) := ⟨T24s3_ok.1⟩
instance : Fact (T24s5.check = true) := ⟨T24s5_ok.1⟩
instance : Fact (T24s7.check = true) := ⟨T24s7_ok.1⟩
instance : Fact (T24s11.check = true) := ⟨T24s11_ok.1⟩
instance : Fact (T24s23.check = true) := ⟨T24s23_ok.1⟩

def mats24s2 : Array (List ℕ) := matsOf11 T24s2

def act24s2 (p : T24s2.Elem) (m : ℕ) : ℕ := actM (mats24s2[p.idx]!) m

def fixTab24 : Array (List ℕ) :=
  Array.ofFn fun i : Fin T24s2.n =>
    let p := T24s2.elemEquiv.symm i
    if p * p = 1 then fixMasks 11 act24s2 [p] else []

def fixMasks24 : List T24s2.Elem → List ℕ
  | [] => fixMasks 11 act24s2 []
  | a :: l => (fixTab24[a.idx]!).filter fun m => l.all fun b => act24s2 b m == m

theorem fixMasks_cons {n : ℕ} {P : Type*} (act : P → ℕ → ℕ) (a : P) (l : List P) :
    fixMasks n act (a :: l) = (fixMasks n act [a]).filter fun m => l.all fun b => act b m == m := by
  simp only [fixMasks, List.filter_filter, List.all_cons, List.all_nil, Bool.and_true]
  congr 1
  funext m
  rw [Bool.and_comm]

theorem fixTab24_get {a : T24s2.Elem} (ha : a * a = 1) :
    fixTab24[a.idx]! = fixMasks 11 act24s2 [a] := by
  rw [fixTab24, getElem!_pos _ a.idx (by simpa using a.lt), Array.getElem_ofFn]
  have : T24s2.elemEquiv.symm ⟨a.idx, a.lt⟩ = a := rfl
  simp only [this, ha, ↓reduceIte]

theorem fixMasks24_eq {l : List T24s2.Elem} (hl : ∀ a ∈ l, a * a = 1)
    :
    fixMasks24 l = fixMasks 11 act24s2 l := by
  cases l with
  | nil => rfl
  | cons a l => rw [fixMasks24, fixTab24_get (hl a List.mem_cons_self), ← fixMasks_cons]

def inv24s2 : List T24s2.Elem := T24s2.invols

def posArr24s2 : Array ℕ := T24s2.posArr inv24s2

def pos24s2 (x : T24s2.Elem) : ℕ := posArr24s2[x.idx]!

theorem pos24s2_eq (x : T24s2.Elem) :
    pos24s2 x = pos inv24s2 x := T24s2.posArr_spec _ x

def pred24 (l : List T24s2.Elem) : Bool :=
  let k := l.length
  let F := fixMasks24 l
  let d := Nat.log 2 F.length
  decide (k ≤ 6) && (k == 0 || !decide (11 - d ≤ k + 1) || avoidOK 11 3 o2Masks24 F) &&
    (k != 1 || decide (4 ≤ 11 - d)) &&
    (k != 6 || xiCheck 11 11 act24s2 l || d == 3)

def odd24OK (T : PT 24) [Fact (T.check = true)] (mats : Array (List ℕ)) : Prop :=
  ∀ p : T.Elem, p ≠ 1 →
    avoidOK 11 3 o2Masks24 (fixMasks 11 (fun q m => actM (mats[q.idx]!) m) [p]) = true

def mats24s3 : Array (List ℕ) := matsOf11 T24s3
def mats24s5 : Array (List ℕ) := matsOf11 T24s5
def mats24s7 : Array (List ℕ) := matsOf11 T24s7
def mats24s11 : Array (List ℕ) := matsOf11 T24s11
def mats24s23 : Array (List ℕ) := matsOf11 T24s23

end CFSG.Quasithin.H.Mathieu
