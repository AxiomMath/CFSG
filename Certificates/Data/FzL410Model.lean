module

public import Certificates.Data.FzL410Norm

public section

namespace Certificates.FzL410

@[expose] def ap (b : ZMod 2) (f : A → A) (q : A) : A := if b = 0 then q else f q

@[expose] def act (v : V) (q : A) : A := ap v.1 tt (ap v.2.1 ss (ap v.2.2 ll q))

@[expose] def mulT (x y : TM) : TM := (x.1 + act x.2 y.1, x.2 + y.2)

@[expose] def oneT : TM := (0, 0)

@[expose] def actR (w : ZMod 2 × ZMod 2) (q : A) : A := ap w.1 tt (ap w.2 ss q)

@[expose] def mulR (x y : RM) : RM := (x.1 + actR x.2 y.1, x.2 + y.2)

@[expose] def oneR : RM := (0, 0)

@[expose] def cMod : ℕ := 67108859

@[expose] def cMix (x y : ℕ) : ℕ := ((x + y) % cMod) * ((x + y) % cMod)

@[expose] def cOrdGo {X : Type} [DecidableEq X] (m : X → X → X) (one x : X) : ℕ → X → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, r, n => if r = one then n else cOrdGo m one x f (m r x) (n + 1)

@[expose] def cOrd {X : Type} [DecidableEq X] (m : X → X → X) (one x : X) : ℕ :=
  cOrdGo m one x 32 x 1

@[expose] def cRound {X : Type} [Fintype X] (m : X → X → X) (c : X → ℕ) (x : X) : ℕ :=
  (∑ y : X, cMix (c y * 1000003) (c (m x y) * 998244353 + 1)) % cMod

@[expose] def c1 {X : Type} [Fintype X] [DecidableEq X] (m : X → X → X) (one : X) (x : X) : ℕ :=
  cRound m (cOrd m one) x

@[expose] def TabSep {X : Type} (pr : X → Prop) (tab : Multiset (X × ℕ)) : Prop :=
  ∀ p ∈ tab, ∀ q ∈ tab, p.2 = q.2 → (pr p.1 ↔ pr q.1)

instance {X : Type} (pr : X → Prop) [DecidablePred pr] (tab : Multiset (X × ℕ)) :
    Decidable (TabSep pr tab) := by
  unfold TabSep; infer_instance

@[expose] def colTab {X : Type} [Fintype X] [DecidableEq X] (m : X → X → X) (one : X) :
    Multiset (X × ℕ) :=
  (Finset.univ : Finset X).val.map fun x => (x, c1 m one x)

theorem tabSep_iff {X : Type} [Fintype X] [DecidableEq X] (m : X → X → X) (one : X)
    (pr : X → Prop) :
    (∀ a b : X, c1 m one a = c1 m one b → (pr a ↔ pr b)) ↔ TabSep pr (colTab m one) := by
  constructor
  · intro h p hp q hq hpq
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hq
    exact h x y hpq
  · intro h a b hab
    exact h (a, c1 m one a) (Multiset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩) (b, c1 m one b)
      (Multiset.mem_map.mpr ⟨b, Finset.mem_univ b, rfl⟩) hab

@[expose] def inR (x : TM) : Prop := x.2.2.2 = 0

@[expose] def inQ (x : TM) : Prop := x.2.2.1 = 0 ∧ x.2.2.2 = 0

@[expose] def inP (x : TM) : Prop := x.2 = 0

@[expose] def EA (a : A) : Prop := a.2.2 = 0

@[expose] def FA (a : A) : Prop := tt (ss a) = a

@[expose] def ZA (a : A) : Prop := a.2.2 = 0 ∧ (2 : ℕ) • a = 0

@[expose] def inZ (x : TM) : Prop := x.2 = 0 ∧ ZA x.1

@[expose] def eE (a b : ZMod 4) : TM := (((a, b, 0, 0) : A), (0 : V))

@[expose] def zE (a b : ZMod 2) : TM :=
  (((2 : ZMod 4) * (a.val : ZMod 4), (2 : ZMod 4) * (b.val : ZMod 4), 0, 0), (0 : V))

@[expose] def pe (a : A) : TM := (a, (0 : V))

@[expose] def tM : TM := (0, (1, 0, 0))

@[expose] def tsM : TM := (0, (1, 1, 0))

instance : DecidablePred inR := fun x => by unfold inR; infer_instance
instance : DecidablePred inQ := fun x => by unfold inQ; infer_instance
instance : DecidablePred inP := fun x => by unfold inP; infer_instance
instance : DecidablePred EA := fun x => by unfold EA; infer_instance
instance : DecidablePred FA := fun x => by unfold FA; infer_instance
instance : DecidablePred ZA := fun x => by unfold ZA; infer_instance
instance : DecidablePred inZ := fun x => by unfold inZ; infer_instance

@[expose] def CharR : Prop := ∀ a b : TM, c1 mulT oneT a = c1 mulT oneT b → (inR a ↔ inR b)

instance : Decidable CharR := decidable_of_iff _ (tabSep_iff mulT oneT inR).symm

@[expose] def CharP : Prop :=
  ∀ a b : RM, c1 mulR oneR a = c1 mulR oneR b → (a.2 = 0 ↔ b.2 = 0)

instance : Decidable CharP :=
  decidable_of_iff (TabSep (fun x : RM => x.2 = 0) (colTab mulR oneR))
    (tabSep_iff mulR oneR (fun x : RM => x.2 = 0)).symm

@[expose] def SqZ : Prop := ∀ x : TM, inR x → inZ (mulT x x)

instance : Decidable SqZ := by unfold SqZ; infer_instance

@[expose] def RQRow (x y : TM) : Prop :=
  ∃ a : ZMod 4, ∃ b : ZMod 4, mulT x y = mulT (mulT (eE a b) y) x

instance (x y : TM) : Decidable (RQRow x y) := by unfold RQRow; infer_instance

@[expose] def RQRow2 (x : TM) : Prop := ∀ y : TM, inQ y → RQRow x y

instance (x : TM) : Decidable (RQRow2 x) := by unfold RQRow2; infer_instance

@[expose] def RQ : Prop := ∀ x : TM, inR x → RQRow2 x

instance : Decidable RQ := by unfold RQ; infer_instance

@[expose] def CentE (x : TM) : Prop :=
  ∀ a : ZMod 4, ∀ b : ZMod 4, mulT x (eE a b) = mulT (eE a b) x

instance (x : TM) : Decidable (CentE x) := by unfold CentE; infer_instance

@[expose] def QC : Prop := ∀ x : TM, inR x → (CentE x ↔ inQ x)

instance : Decidable QC := by unfold QC; infer_instance

@[expose] def EF : Prop := ∀ a : A, EA a → FA a → ZA a

instance : Decidable EF := by unfold EF; infer_instance

@[expose] def CentOf (i : TM) (pr : A → Prop) : Prop :=
  ∀ a : A, (mulT (pe a) i = mulT i (pe a) ↔ pr a)

instance (i : TM) (pr : A → Prop) [DecidablePred pr] : Decidable (CentOf i pr) := by
  unfold CentOf; infer_instance

@[expose] def CentX (i : TM) : Prop :=
  ∀ a : A, mulT (pe a) i = mulT i (pe a) → (2 : ℕ) • a = 0

instance (i : TM) : Decidable (CentX i) := by unfold CentX; infer_instance

@[expose] def CentP : Prop :=
  ∀ i : TM, inR i → ¬ inP i → (CentOf i EA ∨ CentOf i FA ∨ CentX i)

instance : Decidable CentP := by unfold CentP; infer_instance

@[expose] def InvRow (i : TM) : Prop :=
  inR i → ¬ inP i → mulT i i = oneT → CentOf i FA →
    ∃ a : ZMod 4, ∃ b : ZMod 4, i = mulT (eE a b) tsM

instance (i : TM) : Decidable (InvRow i) := by unfold InvRow; infer_instance

@[expose] def InvF : Prop := ∀ i : TM, InvRow i

instance : Decidable InvF := by unfold InvF; infer_instance

@[expose] def CR (i x : TM) : Prop := inR x ∧ mulT x i = mulT i x

instance (i : TM) : DecidablePred (CR i) := fun x => by unfold CR; infer_instance

@[expose] def ZCR (i z : TM) : Prop := CR i z ∧ ∀ c : TM, CR i c → mulT z c = mulT c z

instance (i : TM) : DecidablePred (ZCR i) := fun z => by unfold ZCR; infer_instance

@[expose] def SqPair2 (i x y : TM) : Prop :=
  CR i x ∧ CR i y ∧ mulT x x ≠ oneT ∧ mulT y y ≠ oneT ∧ mulT x x ≠ mulT y y

instance (i x y : TM) : Decidable (SqPair2 i x y) := by unfold SqPair2; infer_instance

@[expose] def SqPair (i : TM) : Prop := ∃ x : TM, ∃ y : TM, SqPair2 i x y

instance (i : TM) : Decidable (SqPair i) := by unfold SqPair; infer_instance

@[expose] def ClsZ (i r : TM) : Prop :=
  inR r → ∃ a : ZMod 2, ∃ b : ZMod 2, mulT r i = mulT (mulT i (zE a b)) r

instance (i r : TM) : Decidable (ClsZ i r) := by unfold ClsZ; infer_instance

@[expose] def ClsAll (i : TM) : Prop := ∀ r : TM, ClsZ i r

instance (i : TM) : Decidable (ClsAll i) := by unfold ClsAll; infer_instance

@[expose] def FusAt (i : TM) : Prop :=
  (Finset.univ.filter (CR i)).card = 64 ∧ SqPair i ∧
    (Finset.univ.filter (ZCR i)).card = 8 ∧ ClsAll i

instance (i : TM) : Decidable (FusAt i) := by unfold FusAt; infer_instance

@[expose] def FusTS (a b : ZMod 4) : Prop := FusAt (mulT (eE a b) tsM)

instance (a b : ZMod 4) : Decidable (FusTS a b) := by unfold FusTS; infer_instance

@[expose] def FusAll : Prop := FusAt tM ∧ ∀ a : ZMod 4, ∀ b : ZMod 4, FusTS a b

instance : Decidable FusAll := by unfold FusAll; infer_instance

@[expose] def inS (x : TM) : Prop := mulT x tM = mulT tM x

instance : DecidablePred inS := fun x => by unfold inS; infer_instance

@[expose] def CardS : Prop := (Finset.univ.filter inS).card = 128

instance : Decidable CardS := by unfold CardS; infer_instance

@[expose] def CS (a b x : TM) : Prop := inS x ∧ mulT x a = mulT a x ∧ mulT x b = mulT b x

instance (a b : TM) : DecidablePred (CS a b) := fun x => by unfold CS; infer_instance

@[expose] def ZCS (a b z : TM) : Prop := CS a b z ∧ ∀ c : TM, CS a b c → mulT z c = mulT c z

instance (a b : TM) : DecidablePred (ZCS a b) := fun z => by unfold ZCS; infer_instance

@[expose] def Exp4 (a b : TM) : Prop :=
  ∀ x : TM, CS a b x → mulT (mulT x x) (mulT x x) = oneT

instance (a b : TM) : Decidable (Exp4 a b) := by unfold Exp4; infer_instance

@[expose] def InCR (a b : TM) : Prop := ∀ x : TM, CS a b x → inR x

instance (a b : TM) : Decidable (InCR a b) := by unfold InCR; infer_instance

@[expose] def SLRow (a b : TM) : Prop :=
  inS a → inS b → mulT a a = oneT → mulT b b = oneT → a ≠ oneT → b ≠ oneT → a ≠ b →
    mulT a b = mulT b a → (Finset.univ.filter (CS a b)).card = 64 → Exp4 a b →
    (Finset.univ.filter (ZCS a b)).card = 8 → InCR a b

instance (a b : TM) : Decidable (SLRow a b) := by unfold SLRow; infer_instance

@[expose] def SLem : Prop := ∀ a : TM, ∀ b : TM, SLRow a b

instance : Decidable SLem := by unfold SLem; infer_instance

@[expose] def ModelFacts : Prop :=
  CharR ∧ CharP ∧ SqZ ∧ RQ ∧ QC ∧ EF ∧ CentP ∧ InvF ∧ FusAll ∧ CardS ∧ SLem

instance : Decidable ModelFacts := by unfold ModelFacts; infer_instance

end Certificates.FzL410
