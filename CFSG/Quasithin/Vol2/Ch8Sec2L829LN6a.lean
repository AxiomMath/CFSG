module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13.L829N

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def toF2L6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (Q : Submodule A W) :
    Submodule (ZMod 2) W where
  carrier := {w | w ∈ Q}
  add_mem' := fun hx hy => Q.add_mem hx hy
  zero_mem' := Q.zero_mem
  smul_mem' := fun c {w} hw => by
    have h := Q.smul_mem (algebraMap (ZMod 2) A c) hw
    have e : (algebraMap (ZMod 2) A c) • w = c • w := by
      show (algebraMap (ZMod 2) (Module.End (ZMod 2) W) c) w = c • w
      rw [Module.algebraMap_end_apply]
    rw [e] at h
    exact h

abbrev ConjOK6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W) : Prop :=
  ∀ a ∈ A, ((t⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) * a * (t : Module.End (ZMod 2) W) ∈ A

@[expose] def twA6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (Q : Submodule A W) : Submodule A W where
  carrier := {w | (t⁻¹ : W ≃ₗ[ZMod 2] W) w ∈ Q}
  add_mem' := fun {x y} hx hy => by
    show (t⁻¹ : W ≃ₗ[ZMod 2] W) (x + y) ∈ Q
    rw [map_add]
    exact Q.add_mem hx hy
  zero_mem' := by
    show (t⁻¹ : W ≃ₗ[ZMod 2] W) 0 ∈ Q
    rw [map_zero]
    exact Q.zero_mem
  smul_mem' := fun a {w} hw => by
    show (t⁻¹ : W ≃ₗ[ZMod 2] W) ((a : Module.End (ZMod 2) W) w) ∈ Q
    have e : (((t⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) * (a : Module.End (ZMod 2) W) *
        (t : Module.End (ZMod 2) W)) ((t⁻¹ : W ≃ₗ[ZMod 2] W) w) =
        (t⁻¹ : W ≃ₗ[ZMod 2] W) ((a : Module.End (ZMod 2) W) w) := by
      simp [Module.End.mul_apply]
    rw [← e]
    exact Q.smul_mem (⟨_, hc a a.2⟩ : A) hw

@[expose] def conjA6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (a : A) : A :=
  ⟨((t⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) * (a : Module.End (ZMod 2) W) *
    (t : Module.End (ZMod 2) W), hc a a.2⟩

@[expose] def psiTw6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (Q : Submodule A W) (w : ↥(twA6 A t hc Q)) : ↥Q :=
  ⟨(t⁻¹ : W ≃ₗ[ZMod 2] W) w.1, w.2⟩

theorem psiTw6_add (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (Q : Submodule A W) (w v : ↥(twA6 A t hc Q)) :
    psiTw6 A t hc Q (w + v) = psiTw6 A t hc Q w + psiTw6 A t hc Q v :=
  Subtype.ext (by simp [psiTw6])

theorem psiTw6_smul (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (Q : Submodule A W) (a : A) (w : ↥(twA6 A t hc Q)) :
    psiTw6 A t hc Q (a • w) = conjA6 A t hc a • psiTw6 A t hc Q w := by
  apply Subtype.ext
  show (t⁻¹ : W ≃ₗ[ZMod 2] W) ((a : Module.End (ZMod 2) W) w.1) =
    ((conjA6 A t hc a : A) : Module.End (ZMod 2) W) ((t⁻¹ : W ≃ₗ[ZMod 2] W) w.1)
  simp [conjA6, Module.End.mul_apply]

theorem conj_apply6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (t : W ≃ₗ[ZMod 2] W) (hc : ConjOK6 A t) (a : A) (y : W) :
    (t : Module.End (ZMod 2) W) (((conjA6 A t hc a : A) : Module.End (ZMod 2) W) y) =
      (a : Module.End (ZMod 2) W) ((t : Module.End (ZMod 2) W) y) := by
  show (t : W ≃ₗ[ZMod 2] W) ((t⁻¹ : W ≃ₗ[ZMod 2] W) ((a : Module.End (ZMod 2) W)
    ((t : W ≃ₗ[ZMod 2] W) y))) = (a : Module.End (ZMod 2) W) ((t : W ≃ₗ[ZMod 2] W) y)
  simp

@[expose] def fwd6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) {Q R : Submodule A W} (e : Q ≃ₗ[A] R)
    (w : ↥(twA6 A t hc Q)) : W :=
  t (e (psiTw6 A t hc Q w)).1

theorem fwd6_mem (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (t : W ≃ₗ[ZMod 2] W) (hc : ConjOK6 A t) {Q R : Submodule A W} (e : Q ≃ₗ[A] R)
    (w : ↥(twA6 A t hc Q)) : fwd6 A t hc e w ∈ twA6 A t hc R := by
  show (t⁻¹ : W ≃ₗ[ZMod 2] W) (t (e (psiTw6 A t hc Q w)).1) ∈ R
  simpa using (e (psiTw6 A t hc Q w)).2

@[expose] def bwd6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) {Q R : Submodule A W} (e : Q ≃ₗ[A] R)
    (w : ↥(twA6 A t hc R)) : W :=
  t (e.symm (psiTw6 A t hc R w)).1

theorem bwd6_mem (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (t : W ≃ₗ[ZMod 2] W) (hc : ConjOK6 A t) {Q R : Submodule A W} (e : Q ≃ₗ[A] R)
    (w : ↥(twA6 A t hc R)) : bwd6 A t hc e w ∈ twA6 A t hc Q := by
  show (t⁻¹ : W ≃ₗ[ZMod 2] W) (t (e.symm (psiTw6 A t hc R w)).1) ∈ Q
  simpa using (e.symm (psiTw6 A t hc R w)).2

@[expose] def twA6Equiv (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) {Q R : Submodule A W} (e : Q ≃ₗ[A] R) :
    twA6 A t hc Q ≃ₗ[A] twA6 A t hc R where
  toFun w := ⟨fwd6 A t hc e w, fwd6_mem A t hc e w⟩
  invFun w := ⟨bwd6 A t hc e w, bwd6_mem A t hc e w⟩
  map_add' := fun w v => Subtype.ext (by simp [fwd6, psiTw6_add, map_add])
  map_smul' := fun a w => Subtype.ext (by
    show fwd6 A t hc e (a • w) = (a : Module.End (ZMod 2) W) (fwd6 A t hc e w)
    rw [fwd6, psiTw6_smul, map_smul]
    exact conj_apply6 A t hc a _)
  left_inv := fun w => Subtype.ext (by
    have h1 : psiTw6 A t hc R ⟨fwd6 A t hc e w, fwd6_mem A t hc e w⟩ = e (psiTw6 A t hc Q w) :=
      Subtype.ext (by simp [psiTw6, fwd6])
    show bwd6 A t hc e ⟨fwd6 A t hc e w, fwd6_mem A t hc e w⟩ = w.1
    rw [bwd6, h1, LinearEquiv.symm_apply_apply]
    simp [psiTw6])
  right_inv := fun w => Subtype.ext (by
    have h1 : psiTw6 A t hc Q ⟨bwd6 A t hc e w, bwd6_mem A t hc e w⟩ = e.symm (psiTw6 A t hc R w) :=
      Subtype.ext (by simp [psiTw6, bwd6])
    show fwd6 A t hc e ⟨bwd6 A t hc e w, bwd6_mem A t hc e w⟩ = w.1
    rw [fwd6, h1, LinearEquiv.apply_symm_apply]
    simp [psiTw6])

end CFSG.Quasithin.H13.L829N
