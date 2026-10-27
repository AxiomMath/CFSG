module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Group.Fin.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open Matrix

abbrev Mat4 : Type := Matrix (Fin 3) (Fin 3) (ZMod 4)

@[expose] def X0 : Mat4 := !![0, 0, 1; 0, 3, 0; 1, 0, 0]

@[expose] def Y0 : Mat4 := !![0, 1, 2; 1, 2, 1; 1, 1, 2]

@[expose] def twoM (m : Fin 3 → Fin 3 → Bool) : Mat4 := Matrix.of fun i j => if m i j then 2 else 0

@[expose] def GenRel (X Y : Mat4) : Prop :=
  X * X = 1 ∧ Y * Y * Y = 1 ∧ (X * Y) ^ 7 = 1 ∧ (X * Y * X * (Y * Y)) ^ 4 = 1

instance (X Y : Mat4) : Decidable (GenRel X Y) := by
  unfold GenRel
  infer_instance

@[expose] def complementA : Prop :=
  ∀ my : Fin 3 → Fin 3 → Bool, (Y0 + twoM my) * (Y0 + twoM my) * (Y0 + twoM my) = 1 →
    ∃ mk : Fin 3 → Fin 3 → Bool, (1 + twoM mk) * (Y0 + twoM my) = Y0 * (1 + twoM mk)

instance : Decidable complementA := by
  unfold complementA
  infer_instance

@[expose] def complementB : Prop :=
  ∀ mx : Fin 3 → Fin 3 → Bool, GenRel (X0 + twoM mx) Y0 →
    ∃ mk : Fin 3 → Fin 3 → Bool, (1 + twoM mk) * Y0 = Y0 * (1 + twoM mk) ∧
      (1 + twoM mk) * (X0 + twoM mx) = X0 * (1 + twoM mk)

instance : Decidable complementB := by
  unfold complementB
  infer_instance

@[expose] def complementOK : Bool := decide complementA && decide complementB

@[expose] def Bm : Mat4 := Y0 * X0 * (Y0 * Y0)

@[expose] def Cm : Mat4 := X0 * Bm

@[expose] def uM : Mat4 :=
  Y0 * X0 * Y0 * X0 * Y0 * Y0 * X0 * Y0 * Y0 * X0 * Y0 * X0 * Y0

@[expose] def d1 : Fin 3 → ZMod 4 := ![1, 2, 3]

@[expose] def tLetter (i : Fin 3) : Fin 5 := Fin.castLE (by decide) i

@[expose] def tInv (v : Fin 3 → ZMod 4) : List (Fin 5 × Bool) :=
  List.replicate (v 2).val (2, false) ++ List.replicate (v 1).val (1, false) ++
    List.replicate (v 0).val (0, false)

@[expose] def actRel (g : Fin 5) (M : Mat4) (i : Fin 3) : List (Fin 5 × Bool) :=
  [(g, true), (tLetter i, true), (g, false)] ++ tInv fun r => M r i

@[expose] def qRels (d : Fin 3 → ZMod 4) : List (List (Fin 5 × Bool)) :=
  [List.replicate 4 (0, true), List.replicate 4 (1, true), List.replicate 4 (2, true),
    [(0, true), (1, true), (0, false), (1, false)], [(0, true), (2, true), (0, false), (2, false)],
    [(1, true), (2, true), (1, false), (2, false)],
    actRel 3 X0 0, actRel 3 X0 1, actRel 3 X0 2, actRel 4 Bm 0, actRel 4 Bm 1, actRel 4 Bm 2,
    [(3, true), (3, true)], [(4, true), (4, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true), (3, true), (4, true)] ++
      tInv d]

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
