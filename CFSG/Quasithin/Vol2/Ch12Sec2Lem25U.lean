module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi

public section

namespace CFSG.Quasithin.H13

namespace Lem25

abbrev B5 : Type := Fin 5 → Fin 5 → Bool

@[expose] def bmul (A B : B5) : B5 := fun i j =>
  (A i 0 && B 0 j) ^^ (A i 1 && B 1 j) ^^ (A i 2 && B 2 j) ^^ (A i 3 && B 3 j) ^^ (A i 4 && B 4 j)

@[expose] def bone : B5 := fun i j => decide (i = j)

@[expose] def ofRows (r0 r1 r2 r3 r4 : List Bool) : B5 := fun i j =>
  ([r0, r1, r2, r3, r4].getD i.val []).getD j.val false

@[expose] def Bh : B5 := ofRows [false, false, true, false, true] [false, false, false, true, false]
  [true, false, true, false, true] [false, true, false, true, false]
  [false, false, false, false, true]

@[expose] def Bvs (p₀ p₁ q₀ q₁ : Bool) : B5 := ofRows [true, false, p₀, q₀, false]
  [false, true, p₁, q₁, false] [false, false, true, false, false] [false, false, false, true, false]
  [false, false, false, false, true]

@[expose] def Bv : B5 := Bvs true false false true

theorem bv_eq_of_inv : ∀ p₀ p₁ q₀ q₁ : Bool,
    bmul (bmul (Bvs p₀ p₁ q₀ q₁) Bh) (Bvs p₀ p₁ q₀ q₁) = bmul Bh Bh →
    Bvs p₀ p₁ q₀ q₁ = Bv := by
  decide

@[expose] def By (a b c d : Bool) (x₃ x₄ : Fin 3 → Bool) : B5 :=
  ofRows [a, b, x₃ 0, x₄ 0, false] [c, d, x₃ 1, x₄ 1, false] [false, false, a, b, false]
    [false, false, c, d, false] [false, false, x₃ 2, x₄ 2, true]

@[expose] def D8 (a b : B5) : Prop :=
  bmul a a = bone ∧ bmul b b = bone ∧
    bmul (bmul (bmul a b) (bmul a b)) (bmul (bmul a b) (bmul a b)) = bone ∧
    bmul (bmul a b) (bmul a b) ≠ bone

instance (a b : B5) : Decidable (D8 a b) := by unfold D8; infer_instance

@[expose] def wA (i : Fin 2) (y : B5) : B5 :=
  match i with
  | 0 => Bv
  | 1 => bmul (bmul (bmul y Bh) (bmul y y)) Bv

@[expose] def wB (j : Fin 5) (y : B5) : B5 :=
  match j with
  | 0 => bmul (bmul (bmul Bh y) (bmul Bh Bh)) (bmul y y)
  | 1 => bmul (bmul (bmul Bh y) Bh) (bmul y y)
  | 2 => bmul (bmul (bmul (bmul (bmul Bh y) Bh) (bmul y y)) Bh) Bv
  | 3 => bmul (bmul (bmul (bmul (bmul Bh y) (bmul Bh Bh)) (bmul y y)) Bh) Bv
  | 4 => bmul (bmul (bmul (bmul (bmul Bh (bmul y y)) (bmul Bh Bh)) y) Bh) Bv

theorem wit_of_cube : ∀ a b c d : Bool, ∀ x₃ x₄ : Fin 3 → Bool,
    bmul (bmul (By a b c d x₃ x₄) (By a b c d x₃ x₄)) (By a b c d x₃ x₄) = bone →
    (a, b, c, d) ≠ (true, false, false, true) →
    ∃ i : Fin 2, ∃ j : Fin 5, D8 (wA i (By a b c d x₃ x₄)) (wB j (By a b c d x₃ x₄)) := by
  decide +kernel

end Lem25

end CFSG.Quasithin.H13
