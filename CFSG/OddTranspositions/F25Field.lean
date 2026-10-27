module

public import CFSG.OddTranspositions.F25Carrier
public import Mathlib.Algebra.Field.MinimalAxioms

public section

namespace CFSG.OddTranspositions.QZ

instance : Field F25t := Field.ofMinimalAxioms F25t
  (by
    intro a b c
    apply F25t.ext
    · change (a.a + b.a) + c.a = a.a + (b.a + c.a); ring
    · change (a.b + b.b) + c.b = a.b + (b.b + c.b); ring)
  (by
    intro a
    apply F25t.ext
    · change (0 : ZMod 5) + a.a = a.a; ring
    · change (0 : ZMod 5) + a.b = a.b; ring)
  (by
    intro a
    apply F25t.ext
    · change (-a.a) + a.a = (0 : ZMod 5); ring
    · change (-a.b) + a.b = (0 : ZMod 5); ring)
  (by
    intro a b c
    apply F25t.ext
    · change (a.a * b.a + 3 * a.b * b.b) * c.a +
        3 * (a.a * b.b + a.b * b.a) * c.b =
        a.a * (b.a * c.a + 3 * b.b * c.b) + 3 * a.b * (b.a * c.b + b.b * c.a)
      ring
    · change (a.a * b.a + 3 * a.b * b.b) * c.b +
        (a.a * b.b + a.b * b.a) * c.a =
        a.a * (b.a * c.b + b.b * c.a) + a.b * (b.a * c.a + 3 * b.b * c.b)
      ring)
  (by
    intro a b
    apply F25t.ext
    · change a.a * b.a + 3 * a.b * b.b = b.a * a.a + 3 * b.b * a.b; ring
    · change a.a * b.b + a.b * b.a = b.a * a.b + b.b * a.a; ring)
  (by
    intro a
    apply F25t.ext
    · change (1 : ZMod 5) * a.a + 3 * 0 * a.b = a.a; ring
    · change (1 : ZMod 5) * a.b + 0 * a.a = a.b; ring)
  (by
    intro x hx
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hn := norm_ne_zero hx
    apply F25t.ext
    · change x.a * (x.a / (x.a ^ 2 - 3 * x.b ^ 2)) +
        3 * x.b * (-x.b / (x.a ^ 2 - 3 * x.b ^ 2)) = 1
      field_simp [hn]
      ring
    · change x.a * (-x.b / (x.a ^ 2 - 3 * x.b ^ 2)) +
        x.b * (x.a / (x.a ^ 2 - 3 * x.b ^ 2)) = 0
      field_simp [hn]
      ring)
  (by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    apply F25t.ext
    · change (0 : ZMod 5) / (0 ^ 2 - 3 * 0 ^ 2) = 0; simp
    · change -(0 : ZMod 5) / (0 ^ 2 - 3 * 0 ^ 2) = 0; simp)
  (by
    intro a b c
    apply F25t.ext
    · change a.a * (b.a + c.a) + 3 * a.b * (b.b + c.b) =
        (a.a * b.a + 3 * a.b * b.b) + (a.a * c.a + 3 * a.b * c.b)
      ring
    · change a.a * (b.b + c.b) + a.b * (b.a + c.a) =
        (a.a * b.b + a.b * b.a) + (a.a * c.b + a.b * c.a)
      ring)
  (by exact ⟨⟨0, 0⟩, ⟨1, 0⟩, by intro h; have := congrArg F25t.a h; exact absurd this (by decide)⟩)

@[simp] theorem add25_def (x y : F25t) :
    x + y = (⟨x.a + y.a, x.b + y.b⟩ : F25t) := rfl

@[simp] theorem mul25_def (x y : F25t) :
    x * y = (⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩ : F25t) := rfl

@[simp] theorem neg25_def (x : F25t) : -x = (⟨-x.a, -x.b⟩ : F25t) := rfl

@[simp] theorem zero25_def : (0 : F25t) = ⟨0, 0⟩ := rfl

@[simp] theorem one25_def : (1 : F25t) = ⟨1, 0⟩ := rfl

section
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[simp] theorem inv25_def (x : F25t) :
    x⁻¹ = (⟨x.a / (x.a ^ 2 - 3 * x.b ^ 2),
      -x.b / (x.a ^ 2 - 3 * x.b ^ 2)⟩ : F25t) := rfl

end

theorem card_F25t_nat : Nat.card F25t = 25 := by
  rw [Nat.card_eq_fintype_card, card_F25t]

end CFSG.OddTranspositions.QZ
