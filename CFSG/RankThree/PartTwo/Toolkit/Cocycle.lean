module

public import CFSG.RankThree.PartTwo.Toolkit.Raw

public section

namespace CFSG.RankThree.PartTwo.Toolkit.Raw

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure V3 where
  x : ZMod 3
  y : ZMod 3
  z : ZMod 3
  deriving Inhabited

@[expose] def V3.beq (v w : V3) : Bool := v.x == w.x && v.y == w.y && v.z == w.z

theorem V3.beq_iff {v w : V3} : v.beq w = true ↔ v = w := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := w
  simp only [V3.beq, Bool.and_eq_true, beq_iff_eq, V3.mk.injEq]
  tauto

instance : DecidableEq V3 := fun _ _ => decidable_of_iff _ V3.beq_iff

@[expose] def vadd (v w : V3) : V3 := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩

@[expose] def vsub (v w : V3) : V3 := ⟨v.x - w.x, v.y - w.y, v.z - w.z⟩

@[expose] def vzero : V3 := ⟨0, 0, 0⟩

@[expose] def rmv (M : R9) (v : V3) : V3 :=
  ⟨M.a*v.x+M.b*v.y+M.c*v.z, M.d*v.x+M.e*v.y+M.f*v.z, M.g*v.x+M.h*v.y+M.i*v.z⟩

@[expose] def ofVec (v : Fin 3 → ZMod 3) : V3 := ⟨v 0, v 1, v 2⟩

@[expose] def toVec (m : V3) : Fin 3 → ZMod 3 := ![m.x, m.y, m.z]

theorem ofVec_toVec (m : V3) : ofVec (toVec m) = m := rfl

theorem ofVec_injective : Function.Injective ofVec := by
  intro v w h
  simp only [ofVec, V3.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  funext i
  fin_cases i <;> assumption

theorem ofVec_add (v w : Fin 3 → ZMod 3) : ofVec (v + w) = vadd (ofVec v) (ofVec w) := rfl

theorem ofVec_sub (v w : Fin 3 → ZMod 3) : ofVec (v - w) = vsub (ofVec v) (ofVec w) := rfl

theorem ofVec_zero : ofVec 0 = vzero := rfl

theorem ofVec_mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (v : Fin 3 → ZMod 3) :
    ofVec (M *ᵥ v) = rmv (ofMat M) (ofVec v) := by
  simp [ofVec, rmv, ofMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[expose] def allV3 : List V3 :=
  vals.flatMap fun a => vals.flatMap fun b => vals.map fun c => ⟨a, b, c⟩

theorem mem_allV3 (v : V3) : v ∈ allV3 := by
  obtain ⟨a, b, c⟩ := v
  have hv : ∀ z : ZMod 3, z ∈ vals := by decide
  simp only [allV3, List.mem_flatMap, List.mem_map]
  exact ⟨a, hv a, b, hv b, c, hv c, rfl⟩

abbrev Word : Type := List (Bool × ℕ)

@[expose] def evalWord {Y : Type*} [Group Y] (a b : Y) : Word → Y
  | [] => 1
  | (s, e) :: w => (if s then b else a) ^ e * evalWord a b w

@[expose] def evalRaw (A B : R9) : Word → R9
  | [] => rone
  | (s, e) :: w => rmul (rpow (if s then B else A) e) (evalRaw A B w)
where
  rpow (M : R9) : ℕ → R9
    | 0 => rone
    | e + 1 => rmul M (rpow M e)

@[expose] def rpowv (M : R9) : ℕ → V3 → V3
  | 0, v => v
  | e + 1, v => rmv M (rpowv M e v)

@[expose] def geom (M : R9) : ℕ → V3 → V3
  | 0, _ => vzero
  | e + 1, v => vadd v (rmv M (geom M e v))

@[expose] def foxRaw (A B : R9) (x₁ x₂ : V3) : Word → V3
  | [] => vzero
  | (s, e) :: w => vadd (geom (if s then B else A) e (if s then x₂ else x₁))
      (rpowv (if s then B else A) e (foxRaw A B x₁ x₂ w))

theorem evalRaw_rpow_ofMat (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (e : ℕ) :
    evalRaw.rpow (ofMat M) e = ofMat (M ^ e) := by
  induction e with
  | zero => rw [evalRaw.rpow, pow_zero, ofMat_one]
  | succ e ih => rw [evalRaw.rpow, ih, pow_succ', ofMat_mul]

theorem ofMat_evalWord_SL (a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) (w : Word) :
    ofMat ((evalWord a b w : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      evalRaw (ofMat (a : Matrix (Fin 3) (Fin 3) (ZMod 3)))
        (ofMat (b : Matrix (Fin 3) (Fin 3) (ZMod 3))) w := by
  induction w with
  | nil => rw [evalWord, evalRaw, Matrix.SpecialLinearGroup.coe_one, ofMat_one]
  | cons p w ih =>
    obtain ⟨s, e⟩ := p
    rw [evalWord, evalRaw, Matrix.SpecialLinearGroup.coe_mul, ofMat_mul, ih,
      Matrix.SpecialLinearGroup.coe_pow]
    cases s <;> simp [evalRaw_rpow_ofMat]

theorem evalWord_eq_one_SL {a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)} {w : Word}
    (h : evalRaw (ofMat (a : Matrix (Fin 3) (Fin 3) (ZMod 3)))
      (ofMat (b : Matrix (Fin 3) (Fin 3) (ZMod 3))) w = rone) : evalWord a b w = 1 := by
  apply Subtype.ext
  apply ofMat_injective
  rw [ofMat_evalWord_SL, h, Matrix.SpecialLinearGroup.coe_one, ofMat_one]

theorem map_evalWord {Y Z : Type*} [Group Y] [Group Z] (f : Y →* Z) (a b : Y) (w : Word) :
    f (evalWord a b w) = evalWord (f a) (f b) w := by
  induction w with
  | nil => rw [evalWord, evalWord, map_one]
  | cons p w ih =>
    obtain ⟨s, e⟩ := p
    rw [evalWord, evalWord, map_mul, ih, map_pow]
    cases s <;> rfl

variable {Y : Type*} [Group Y]

@[expose] def IsCocycle {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (σ : Representation (ZMod 3) Y V) (c : Y → V) : Prop :=
  ∀ y z : Y, c (y * z) = σ y (c z) + c y

section Cocycle

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] {σ : Representation (ZMod 3) Y V}
  {c : Y → V}

theorem IsCocycle.map_one (hc : IsCocycle σ c) : c 1 = 0 := by
  have h : c 1 = c 1 + c 1 := by
    have h1 := hc 1 1
    rwa [one_mul, σ.map_one, Module.End.one_apply] at h1
  exact add_eq_left.1 h.symm

theorem IsCocycle.map_inv (hc : IsCocycle σ c) (y : Y) : c y⁻¹ = -σ y⁻¹ (c y) := by
  have h := hc y⁻¹ y
  rw [inv_mul_cancel, hc.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem IsCocycle.eq_of_closure_eq_top {c' : Y → V} (hc : IsCocycle σ c) (hc' : IsCocycle σ c')
    {S : Set Y} (hS : Subgroup.closure S = ⊤) (h : ∀ s ∈ S, c s = c' s) : c = c' := by
  let H : Subgroup Y :=
    { carrier := {y | c y = c' y}
      mul_mem' := fun {y z} hy hz => by
        change c (y * z) = c' (y * z)
        rw [hc, hc', show c z = c' z from hz, show c y = c' y from hy]
      one_mem' := by
        change c 1 = c' 1
        rw [hc.map_one, hc'.map_one]
      inv_mem' := fun {y} hy => by
        change c y⁻¹ = c' y⁻¹
        rw [hc.map_inv, hc'.map_inv, show c y = c' y from hy] }
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 h
  rw [hS] at hle
  funext y
  exact hle (Subgroup.mem_top y)

theorem isCocycle_coboundary (m : V) : IsCocycle σ fun y => σ y m - m := by
  intro y z
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem IsCocycle.map_pow (hc : IsCocycle σ c) (y : Y) (e : ℕ) :
    c (y ^ (e + 1)) = c y + σ y (c (y ^ e)) := by
  rw [pow_succ', hc, add_comm]

end Cocycle

section Fox

variable {σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)} {c : Y → Fin 3 → ZMod 3}

theorem rpowv_ofMat {M : Matrix (Fin 3) (Fin 3) (ZMod 3)} {y : Y}
    (hM : ∀ v, σ y v = M *ᵥ v) (e : ℕ) (v : Fin 3 → ZMod 3) :
    rpowv (ofMat M) e (ofVec v) = ofVec (σ (y ^ e) v) := by
  induction e with
  | zero => rw [rpowv, pow_zero, map_one, Module.End.one_apply]
  | succ e ih => rw [rpowv, ih, pow_succ', map_mul, Module.End.mul_apply, hM, ofVec_mulVec]

theorem IsCocycle.geom_ofMat (hc : IsCocycle σ c) {M : Matrix (Fin 3) (Fin 3) (ZMod 3)} {y : Y}
    (hM : ∀ v, σ y v = M *ᵥ v) (e : ℕ) :
    geom (ofMat M) e (ofVec (c y)) = ofVec (c (y ^ e)) := by
  induction e with
  | zero => rw [geom, pow_zero, hc.map_one, ofVec_zero]
  | succ e ih => rw [geom, ih, hc.map_pow, ofVec_add, hM, ofVec_mulVec]

theorem IsCocycle.ofVec_evalWord (hc : IsCocycle σ c) {a b : Y}
    {A B : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hA : ∀ v, σ a v = A *ᵥ v)
    (hB : ∀ v, σ b v = B *ᵥ v) (w : Word) :
    ofVec (c (evalWord a b w)) = foxRaw (ofMat A) (ofMat B) (ofVec (c a)) (ofVec (c b)) w := by
  induction w with
  | nil => rw [evalWord, foxRaw, hc.map_one, ofVec_zero]
  | cons p w ih =>
    obtain ⟨s, e⟩ := p
    rw [evalWord, foxRaw, hc, add_comm (σ _ _), ofVec_add, ← ih]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hc.geom_ofMat hA, rpowv_ofMat hA]
    · simp only [↓reduceIte]
      rw [hc.geom_ofMat hB, rpowv_ofMat hB]

theorem IsCocycle.foxRaw_eq_zero (hc : IsCocycle σ c) {a b : Y}
    {A B : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hA : ∀ v, σ a v = A *ᵥ v)
    (hB : ∀ v, σ b v = B *ᵥ v) {w : Word} (hw : evalWord a b w = 1) :
    foxRaw (ofMat A) (ofMat B) (ofVec (c a)) (ofVec (c b)) w = vzero := by
  rw [← hc.ofVec_evalWord hA hB, hw, hc.map_one, ofVec_zero]

end Fox

end CFSG.RankThree.PartTwo.Toolkit.Raw
