module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace Certificates.FzL410

abbrev A : Type := ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2

abbrev V : Type := ZMod 2 × ZMod 2 × ZMod 2

abbrev TM : Type := A × V

abbrev RM : Type := A × (ZMod 2 × ZMod 2)

instance : DecidableEq A := inferInstanceAs (DecidableEq (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2))

instance : Fintype A := inferInstanceAs (Fintype (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2))

instance : DecidableEq V := inferInstanceAs (DecidableEq (ZMod 2 × ZMod 2 × ZMod 2))

instance : Fintype V := inferInstanceAs (Fintype (ZMod 2 × ZMod 2 × ZMod 2))

instance : DecidableEq TM := inferInstanceAs (DecidableEq (A × V))

instance : Fintype TM := inferInstanceAs (Fintype (A × V))

instance : DecidableEq RM := inferInstanceAs (DecidableEq (A × (ZMod 2 × ZMod 2)))

instance : Fintype RM := inferInstanceAs (Fintype (A × (ZMod 2 × ZMod 2)))

@[expose] def ev (g1 g2 g3 g4 p : A) : A :=
  p.1.val • g1 + p.2.1.val • g2 + p.2.2.1.val • g3 + p.2.2.2.val • g4

@[expose] def rho (p : A) : A := (-p.2.1, p.1 - p.2.1, p.2.2.2, p.2.2.1 + p.2.2.2)

@[expose] def tt (p : A) : A :=
  (p.1 + 2 * (p.2.2.1.val : ZMod 4), p.2.1 + 2 * (p.2.2.2.val : ZMod 4), p.2.2.1, p.2.2.2)

@[expose] def ss (p : A) : A := (-p.1, -p.2.1, p.2.2.1, p.2.2.2)

@[expose] def ll (p : A) : A := (p.2.1, p.1, p.2.2.2, p.2.2.1)

@[expose] def IsRho3 (g1 g2 g3 g4 : A) : Prop :=
  (∀ p, ev g1 g2 g3 g4 (ev g1 g2 g3 g4 (ev g1 g2 g3 g4 p)) = p) ∧
    (∀ p, ev g1 g2 g3 g4 p = p → p = 0)

instance (g1 g2 g3 g4 : A) : Decidable (IsRho3 g1 g2 g3 g4) := by
  unfold IsRho3; infer_instance

@[expose] def ConjRho (g1 g2 g3 g4 a b : A) : Prop :=
  (2 : ℕ) • b = 0 ∧
    (∀ p, ev g1 g2 g3 g4 (ev a (ev g1 g2 g3 g4 a) b (ev g1 g2 g3 g4 b) p)
        = ev a (ev g1 g2 g3 g4 a) b (ev g1 g2 g3 g4 b) (rho p)) ∧
    (∀ p, ev a (ev g1 g2 g3 g4 a) b (ev g1 g2 g3 g4 b) p = 0 → p = 0)

instance (g1 g2 g3 g4 a b : A) : Decidable (ConjRho g1 g2 g3 g4 a b) := by
  unfold ConjRho; infer_instance

@[expose] def NormRow (g1 g2 g3 g4 : A) : Prop :=
  IsRho3 g1 g2 g3 g4 → ∃ a : A, ∃ b : A, ConjRho g1 g2 g3 g4 a b

instance (g1 g2 g3 g4 : A) : Decidable (NormRow g1 g2 g3 g4) := by
  unfold NormRow; infer_instance

@[expose] def NormSpec : Prop :=
  ∀ g1 : A, ∀ g2 : A, ∀ g3 : A, (2 : ℕ) • g3 = 0 → ∀ g4 : A, (2 : ℕ) • g4 = 0 →
    NormRow g1 g2 g3 g4

instance : Decidable NormSpec := by unfold NormSpec; infer_instance

@[expose] def evEq (c d : A) : A → A := ev c (rho c) d (rho d)

@[expose] def evAn (c d : A) : A → A := ev c (rho (rho c)) d (rho (rho d))

@[expose] def IsT (c d : A) : Prop :=
  (2 : ℕ) • d = 0 ∧ (∀ p, evEq c d (evEq c d p) = p) ∧
    (Finset.univ.filter fun p : A => evEq c d p = p).card = 16 ∧
    (Finset.univ.filter fun p : A => evEq c d p = p ∧ (2 : ℕ) • p = 0).card = 4

instance (c d : A) : Decidable (IsT c d) := by unfold IsT; infer_instance

@[expose] def PsiA (c d c0 d0 : A) : Prop :=
  (2 : ℕ) • d0 = 0 ∧ (∀ p, evEq c0 d0 (evEq c d p) = tt (evEq c0 d0 p)) ∧
    (∀ p, evEq c0 d0 (rho p) = rho (evEq c0 d0 p)) ∧ (∀ p, evEq c0 d0 p = 0 → p = 0)

instance (c d c0 d0 : A) : Decidable (PsiA c d c0 d0) := by unfold PsiA; infer_instance

@[expose] def RowA (c d : A) : Prop := IsT c d → ∃ c0 : A, ∃ d0 : A, PsiA c d c0 d0

instance (c d : A) : Decidable (RowA c d) := by unfold RowA; infer_instance

@[expose] def StageA : Prop := ∀ c : A, ∀ d : A, RowA c d

instance : Decidable StageA := by unfold StageA; infer_instance

@[expose] def IsS (c' d' : A) : Prop :=
  (2 : ℕ) • d' = 0 ∧ (∀ p, evEq c' d' (evEq c' d' p) = p) ∧
    (∀ p, tt (evEq c' d' p) = evEq c' d' (tt p)) ∧ (∀ p, tt p = p → evEq c' d' p = -p)

instance (c' d' : A) : Decidable (IsS c' d') := by unfold IsS; infer_instance

@[expose] def IsL (c' d' l1 l3 : A) : Prop :=
  (2 : ℕ) • l3 = 0 ∧ (∀ p, evAn l1 l3 (evAn l1 l3 p) = p) ∧
    (∀ p, tt (evAn l1 l3 p) = evAn l1 l3 (tt p)) ∧
    (∀ p, evEq c' d' (evAn l1 l3 p) = evAn l1 l3 (evEq c' d' p))

instance (c' d' l1 l3 : A) : Decidable (IsL c' d' l1 l3) := by unfold IsL; infer_instance

@[expose] def SameS (c' d' c0 d0 : A) : Prop :=
  (∀ p, evEq c0 d0 (evEq c' d' p) = ss (evEq c0 d0 p)) ∨
    (∀ p, evEq c0 d0 (evEq c' d' p) = ss (tt (evEq c0 d0 p)))

instance (c' d' c0 d0 : A) : Decidable (SameS c' d' c0 d0) := by unfold SameS; infer_instance

@[expose] def CommTt (c0 d0 : A) : Prop := ∀ p, evEq c0 d0 (tt p) = tt (evEq c0 d0 p)

instance (c0 d0 : A) : Decidable (CommTt c0 d0) := by unfold CommTt; infer_instance

@[expose] def ConjLl (l1 l3 c0 d0 : A) : Prop :=
  ∀ p, evEq c0 d0 (evAn l1 l3 p) = ll (evEq c0 d0 p)

instance (l1 l3 c0 d0 : A) : Decidable (ConjLl l1 l3 c0 d0) := by unfold ConjLl; infer_instance

@[expose] def CommRho (c0 d0 : A) : Prop := ∀ p, evEq c0 d0 (rho p) = rho (evEq c0 d0 p)

instance (c0 d0 : A) : Decidable (CommRho c0 d0) := by unfold CommRho; infer_instance

@[expose] def InjPsi (c0 d0 : A) : Prop := ∀ p, evEq c0 d0 p = 0 → p = 0

instance (c0 d0 : A) : Decidable (InjPsi c0 d0) := by unfold InjPsi; infer_instance

@[expose] def PsiB (c' d' l1 l3 c0 d0 : A) : Prop :=
  (2 : ℕ) • d0 = 0 ∧ ConjLl l1 l3 c0 d0 ∧ SameS c' d' c0 d0 ∧ CommTt c0 d0 ∧ CommRho c0 d0 ∧
    InjPsi c0 d0

instance (c' d' l1 l3 c0 d0 : A) : Decidable (PsiB c' d' l1 l3 c0 d0) := by
  unfold PsiB; infer_instance

@[expose] def psiCands : List (A × A) :=
  [((0, 1, 0, 0), (0, 0, 0, 1)),
  ((0, 1, 0, 0), (0, 2, 0, 1)),
  ((0, 1, 0, 0), (2, 0, 0, 1)),
  ((0, 1, 0, 0), (2, 2, 0, 1)),
  ((0, 3, 0, 0), (0, 0, 0, 1)),
  ((0, 3, 0, 0), (0, 2, 0, 1)),
  ((0, 3, 0, 0), (2, 0, 0, 1)),
  ((0, 3, 0, 0), (2, 2, 0, 1)),
  ((1, 0, 0, 0), (0, 0, 1, 0)),
  ((1, 0, 0, 0), (0, 2, 1, 0)),
  ((1, 0, 0, 0), (2, 0, 1, 0)),
  ((1, 0, 0, 0), (2, 2, 1, 0)),
  ((1, 1, 0, 0), (0, 0, 1, 1)),
  ((1, 1, 0, 0), (0, 2, 1, 1)),
  ((1, 1, 0, 0), (2, 0, 1, 1)),
  ((1, 1, 0, 0), (2, 2, 1, 1)),
  ((1, 2, 0, 0), (0, 0, 1, 0)),
  ((1, 2, 0, 0), (0, 2, 1, 0)),
  ((1, 2, 0, 0), (2, 0, 1, 0)),
  ((1, 2, 0, 0), (2, 2, 1, 0)),
  ((1, 3, 0, 0), (0, 0, 1, 1)),
  ((1, 3, 0, 0), (0, 2, 1, 1)),
  ((1, 3, 0, 0), (2, 0, 1, 1)),
  ((1, 3, 0, 0), (2, 2, 1, 1)),
  ((2, 1, 0, 0), (0, 0, 0, 1)),
  ((2, 1, 0, 0), (0, 2, 0, 1)),
  ((2, 1, 0, 0), (2, 0, 0, 1)),
  ((2, 1, 0, 0), (2, 2, 0, 1)),
  ((2, 3, 0, 0), (0, 0, 0, 1)),
  ((2, 3, 0, 0), (0, 2, 0, 1)),
  ((2, 3, 0, 0), (2, 0, 0, 1)),
  ((2, 3, 0, 0), (2, 2, 0, 1)),
  ((3, 0, 0, 0), (0, 0, 1, 0)),
  ((3, 0, 0, 0), (0, 2, 1, 0)),
  ((3, 0, 0, 0), (2, 0, 1, 0)),
  ((3, 0, 0, 0), (2, 2, 1, 0)),
  ((3, 1, 0, 0), (0, 0, 1, 1)),
  ((3, 1, 0, 0), (0, 2, 1, 1)),
  ((3, 1, 0, 0), (2, 0, 1, 1)),
  ((3, 1, 0, 0), (2, 2, 1, 1)),
  ((3, 2, 0, 0), (0, 0, 1, 0)),
  ((3, 2, 0, 0), (0, 2, 1, 0)),
  ((3, 2, 0, 0), (2, 0, 1, 0)),
  ((3, 2, 0, 0), (2, 2, 1, 0)),
  ((3, 3, 0, 0), (0, 0, 1, 1)),
  ((3, 3, 0, 0), (0, 2, 1, 1)),
  ((3, 3, 0, 0), (2, 0, 1, 1)),
  ((3, 3, 0, 0), (2, 2, 1, 1))]

@[expose] def RowL (c' d' l1 l3 : A) : Prop :=
  IsL c' d' l1 l3 → ∃ ψ ∈ psiCands, PsiB c' d' l1 l3 ψ.1 ψ.2

instance (c' d' l1 l3 : A) : Decidable (RowL c' d' l1 l3) := by unfold RowL; infer_instance

@[expose] def RowS (c' d' : A) : Prop :=
  IsS c' d' → ∀ l1 : A, ∀ l3 : A, RowL c' d' l1 l3

instance (c' d' : A) : Decidable (RowS c' d') := by unfold RowS; infer_instance

@[expose] def StageB : Prop := ∀ c' : A, ∀ d' : A, RowS c' d'

instance : Decidable StageB := by unfold StageB; infer_instance

@[expose] def NormTriple : Prop := NormSpec ∧ StageA ∧ StageB

instance : Decidable NormTriple := by unfold NormTriple; infer_instance

end Certificates.FzL410
