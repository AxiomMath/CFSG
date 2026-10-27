module

public import CFSG.Quasithin.EmptyFaithful.S143KD

public section

namespace CFSG.Quasithin.S143

namespace A6Model

open Multiplicative

@[expose] def Tz : Mat4 :=
  ⟨⟨true, false, false, false⟩, ⟨false, true, false, false⟩, ⟨false, false, true, false⟩,
    ⟨true, false, false, true⟩⟩

@[expose] def rawD (w : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) : Fin 6 → ZMod 2 :=
  n6Norm σ w + n6Norm 1 w

theorem rawD_even (w : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) : ∑ i, rawD w σ i = 0 := by
  simp only [rawD, Pi.add_apply, Finset.sum_add_distrib, n6Norm_sum]
  generalize ∑ i, w i = x
  revert x
  decide

theorem rawD_last (w : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) : rawD w σ 5 = 0 := by
  simp only [rawD, Pi.add_apply, n6Norm_last, add_zero]

@[expose] def dW (w : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) : N6 :=
  ⟨ofAdd (rawD w σ), mem_n6Sub_iff.2 ⟨by rw [toAdd_ofAdd]; exact rawD_even w σ,
    by rw [toAdd_ofAdd]; exact rawD_last w σ⟩⟩

theorem dW_eq_one_iff (w : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) :
    dW w σ = 1 ↔ rawD w σ = 0 := by
  constructor
  · intro h
    have := congrArg (fun a : N6 => toAdd a.1) h
    simpa [dW] using this
  · intro h
    apply Subtype.ext
    show ofAdd (rawD w σ) = 1
    rw [h]
    rfl

theorem dW_add (w w' : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) :
    dW (w + w') σ = dW w σ * dW w' σ := by
  apply Subtype.ext
  show ofAdd (rawD (w + w') σ) = ofAdd (rawD w σ) * ofAdd (rawD w' σ)
  rw [← ofAdd_add]
  congr 1
  simp only [rawD, n6Norm_add]
  ring

theorem dW_principal_of_even {w : Fin 6 → ZMod 2} (hw : ∑ i, w i = 0) :
    ∃ a : N6, ∀ σ : Equiv.Perm (Fin 6), dW w σ = n6Act σ a * a⁻¹ := by
  have hlast : n6Norm 1 w 5 = 0 := n6Norm_last 1 w
  have hsum : ∑ i, n6Norm 1 w i = 0 := by rw [n6Norm_sum]; exact hw
  refine ⟨⟨ofAdd (n6Norm 1 w), mem_n6Sub_iff.2 ⟨by rw [toAdd_ofAdd]; exact hsum,
    by rw [toAdd_ofAdd]; exact hlast⟩⟩, fun σ => ?_⟩
  have hinv : ∀ b : N6, b⁻¹ = b := fun b => inv_eq_of_mul_eq_one_right (n6_mul_self b)
  rw [hinv]
  apply Subtype.ext
  apply toAdd.injective
  funext i
  show rawD w σ i = _
  show rawD w σ i = toAdd (n6Act σ _).1 i + n6Norm 1 w i
  rw [n6Act_val]
  simp only [toAdd_ofAdd, rawD, Pi.add_apply, n6Norm, inv_one, Equiv.Perm.coe_one, id_eq]
  have h5 : ∀ x : ZMod 2, x * 3 = x := by decide
  ring_nf
  rw [h5]


@[expose] def mat4Eq (A B : Mat4) : Bool :=
  (A.r0.x0 == B.r0.x0) && (A.r0.x1 == B.r0.x1) && (A.r0.x2 == B.r0.x2) && (A.r0.x3 == B.r0.x3) &&
  (A.r1.x0 == B.r1.x0) && (A.r1.x1 == B.r1.x1) && (A.r1.x2 == B.r1.x2) && (A.r1.x3 == B.r1.x3) &&
  (A.r2.x0 == B.r2.x0) && (A.r2.x1 == B.r2.x1) && (A.r2.x2 == B.r2.x2) && (A.r2.x3 == B.r2.x3) &&
  (A.r3.x0 == B.r3.x0) && (A.r3.x1 == B.r3.x1) && (A.r3.x2 == B.r3.x2) && (A.r3.x3 == B.r3.x3)

theorem mat4Eq_iff {A B : Mat4} : mat4Eq A B = true ↔ A = B := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1', c2', c3⟩, ⟨d0, d1, d2, d3⟩⟩ := A
  obtain ⟨⟨a0', a1', a2', a3'⟩, ⟨b0', b1', b2', b3'⟩, ⟨c0', c1'', c2'', c3'⟩,
    ⟨d0', d1', d2', d3'⟩⟩ := B
  simp only [mat4Eq, Bool.and_eq_true, beq_iff_eq, Mat4.mk.injEq, V4.mk.injEq]
  tauto


theorem Tz_sq : mm Tz Tz = I4 :=
  mat4Eq_iff.mp (by decide +kernel)

@[expose] def VanL (Vl : List (Equiv.Perm (Fin 6))) (w : Fin 6 → ZMod 2) : Prop :=
  ∀ σ ∈ Vl, rawD w σ = 0

instance (Vl : List (Equiv.Perm (Fin 6))) (w : Fin 6 → ZMod 2) : Decidable (VanL Vl w) := by
  unfold VanL; infer_instance

@[expose] def EquiS (s : Equiv.Perm (Fin 6)) (w : Fin 6 → ZMod 2) : Prop :=
  ∀ σ : Equiv.Perm (Fin 6), σ.sign = 1 → rawD w (s * σ * s⁻¹) = n6Norm s (rawD w σ)

instance (s : Equiv.Perm (Fin 6)) (w : Fin 6 → ZMod 2) : Decidable (EquiS s w) := by
  unfold EquiS; infer_instance

@[expose] def wEven (w : Fin 6 → ZMod 2) : Prop := ∑ i, w i = 0

instance (w : Fin 6 → ZMod 2) : Decidable (wEven w) := by unfold wEven; infer_instance

@[expose] def Fw (w : Fin 6 → ZMod 2) : Equiv.Perm (Fin 6) → (Fin 6 → ZMod 2) :=
  fun σ => if σ.sign = 1 then rawD w σ else 0

structure Conf6 (c : Mat4) (Vl : List (Equiv.Perm (Fin 6))) (s : Equiv.Perm (Fin 6)) : Prop where
  sign_V : ∀ σ ∈ Vl, σ.sign = 1
  s_sign : s.sign = -1
  s_sq : s * s = 1
  s_mat : mat4Eq (mm c (matOf6 s)) (mm Tz c) = true
  m1 : ((Finset.univ.filter (VanL Vl)).image Fw).card ≤ 4
  m2 : ∀ w, VanL Vl w → EquiS s w → wEven w

theorem Conf6.s_eq {c : Mat4} {Vl : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)}
    (h : Conf6 c Vl s) : mm c (matOf6 s) = mm Tz c :=
  mat4Eq_iff.mp h.s_mat

@[expose] def Vl1 : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 0 5 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 2 5, Equiv.swap 0 2 * Equiv.swap 1 5]

@[expose] def Vl2 : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 1 3 * Equiv.swap 2 5, Equiv.swap 1 2 * Equiv.swap 3 5, Equiv.swap 1 5 * Equiv.swap 2 3]

set_option maxRecDepth 100000 in
theorem conf6_one : Conf6 c1 Vl1 (Equiv.swap 3 4) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem conf6_two : Conf6 c2 Vl2 (Equiv.swap 0 4) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

end A6Model

end CFSG.Quasithin.S143
