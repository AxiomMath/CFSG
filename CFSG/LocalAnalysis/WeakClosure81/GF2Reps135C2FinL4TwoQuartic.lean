module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoInner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoPacked

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.Sporadic.SmallF2.Native

@[expose] def qpoly {R : Type*} [Semiring R] (a : R) : R := a * a * a * a + a + 1

theorem qpoly_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (c : V ≃ₗ[ZMod 2] V)
    (f : V →ₗ[ZMod 2] V) :
    qpoly ((c : V →ₗ[ZMod 2] V) ∘ₗ f ∘ₗ (c.symm : V →ₗ[ZMod 2] V)) =
      (c : V →ₗ[ZMod 2] V) ∘ₗ qpoly f ∘ₗ (c.symm : V →ₗ[ZMod 2] V) := by
  apply LinearMap.ext
  intro v
  simp [qpoly, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearEquiv.symm_apply_apply]

theorem finrank_range_qpoly_eq_of_twist {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) (d : V ≃ₗ[ZMod 2] V) (b g g' : SL4)
    (hd : ∀ v, d (ρ g v) = ρ (b * g' * b⁻¹) (d v)) :
    finrank (ZMod 2) (LinearMap.range (qpoly (ρ g : V →ₗ[ZMod 2] V))) =
      finrank (ZMod 2) (LinearMap.range (qpoly (ρ g' : V →ₗ[ZMod 2] V))) := by
  have h1 : ((ρ (b * g' * b⁻¹) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
      (d : V →ₗ[ZMod 2] V) ∘ₗ (ρ g : V →ₗ[ZMod 2] V) ∘ₗ (d.symm : V →ₗ[ZMod 2] V) := by
    apply LinearMap.ext
    intro v
    simp only [LinearEquiv.coe_coe, LinearMap.comp_apply]
    rw [hd, LinearEquiv.apply_symm_apply]
  have h2 : ((ρ (b * g' * b⁻¹) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
      (ρ b : V →ₗ[ZMod 2] V) ∘ₗ (ρ g' : V →ₗ[ZMod 2] V) ∘ₗ ((ρ b).symm : V →ₗ[ZMod 2] V) := by
    apply LinearMap.ext
    intro v
    rw [map_mul, map_mul, map_inv]
    rfl
  calc finrank (ZMod 2) (LinearMap.range (qpoly (ρ g : V →ₗ[ZMod 2] V)))
      = finrank (ZMod 2) (LinearMap.range ((d : V →ₗ[ZMod 2] V) ∘ₗ
          qpoly (ρ g : V →ₗ[ZMod 2] V) ∘ₗ (d.symm : V →ₗ[ZMod 2] V))) :=
        (finrank_range_conj d _).symm
    _ = finrank (ZMod 2) (LinearMap.range (qpoly ((d : V →ₗ[ZMod 2] V) ∘ₗ
          (ρ g : V →ₗ[ZMod 2] V) ∘ₗ (d.symm : V →ₗ[ZMod 2] V)))) := by rw [qpoly_conj]
    _ = finrank (ZMod 2) (LinearMap.range (qpoly ((ρ b : V →ₗ[ZMod 2] V) ∘ₗ
          (ρ g' : V →ₗ[ZMod 2] V) ∘ₗ ((ρ b).symm : V →ₗ[ZMod 2] V)))) := by rw [← h1, h2]
    _ = finrank (ZMod 2) (LinearMap.range ((ρ b : V →ₗ[ZMod 2] V) ∘ₗ
          qpoly (ρ g' : V →ₗ[ZMod 2] V) ∘ₗ ((ρ b).symm : V →ₗ[ZMod 2] V))) := by
        rw [qpoly_conj]
    _ = finrank (ZMod 2) (LinearMap.range (qpoly (ρ g' : V →ₗ[ZMod 2] V))) :=
        finrank_range_conj (ρ b) _

theorem equiv_act_qpoly {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (f : V →ₗ[ZMod 2] V)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (h : ∀ v, e (f v) = A *ᵥ e v) (v : V) :
    e (qpoly f v) = qpoly A *ᵥ e v := by
  simp only [qpoly, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add, h,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem finrank_range_qpoly_eq_of_intertwine {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {d : ℕ} (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (f : V →ₗ[ZMod 2] V)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (h : ∀ v, e (f v) = A *ᵥ e v) :
    finrank (ZMod 2) (LinearMap.range (qpoly f)) =
      finrank (ZMod 2) (LinearMap.range (qpoly A).mulVecLin) :=
  finrank_range_eq_of_intertwine e _ _ (equiv_act_qpoly e f A h)

@[expose] def colAdd (d : ℕ) (X Y : Array ℕ) : Array ℕ :=
  Array.ofFn (n := d) fun k => X[k.val]! ^^^ Y[k.val]!

theorem getElem!_colAdd (d : ℕ) (X Y : Array ℕ) (k : Fin d) :
    (colAdd d X Y)[k.val]! = X[k.val]! ^^^ Y[k.val]! := by
  rw [getElem!_eq_getElem?_getD, colAdd]
  simp only [Array.getElem?_ofFn, k.isLt, ↓reduceDIte, Option.getD_some]

theorem refMat_colAdd (d : ℕ) (X Y : Array ℕ) :
    refMat d (colAdd d X Y) = refMat d X + refMat d Y := by
  ext m k
  rw [refMat, Matrix.of_apply, getElem!_colAdd, Matrix.add_apply, refMat, Matrix.of_apply,
    refMat, Matrix.of_apply, Nat.testBit_xor]
  cases (X[k.val]!).testBit m.val <;> cases (Y[k.val]!).testBit m.val <;> decide

@[expose] def colQpoly (d : ℕ) (C : Array ℕ) : Array ℕ :=
  colAdd d (colAdd d (colMul d (colMul d (colMul d C C) C) C) C) (idRows d)

theorem refMat_colQpoly (d : ℕ) (C : Array ℕ) : refMat d (colQpoly d C) = qpoly (refMat d C) := by
  rw [colQpoly, refMat_colAdd, refMat_colAdd, refMat_colMul, refMat_colMul, refMat_colMul,
    refMat_idRows, qpoly]

end CFSG.LocalAnalysis.WeakClosure81
