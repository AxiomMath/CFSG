module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.H13.P5

abbrev Vec5 : Type := Fin 5 → ZMod 2

@[expose] def crdM : Matrix (Fin 5) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1]

@[expose] def secM : Matrix (Fin 6) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0]

@[expose] def crd (x : Fin 6 → ZMod 2) : Vec5 := crdM.mulVec x

@[expose] def sec (v : Vec5) : Fin 6 → ZMod 2 := secM.mulVec v

@[expose] def act (σ : Equiv.Perm (Fin 6)) (v : Vec5) : Vec5 :=
  crd fun i => sec v (σ⁻¹ i)

theorem crd_add (x y : Fin 6 → ZMod 2) : crd (x + y) = crd x + crd y := Matrix.mulVec_add _ _ _

theorem crd_const : ∀ c : ZMod 2, crd (fun _ => c) = 0 := by decide

theorem crd_sec : ∀ v : Vec5, crd (sec v) = v := by decide +kernel

theorem sec_crd_aux : ∀ x : Fin 6 → ZMod 2, sec (crd x) = x ∨ sec (crd x) = x + fun _ => 1 := by
  decide +kernel

theorem crd_eq_zero_aux : ∀ x : Fin 6 → ZMod 2, crd x = 0 → x = 0 ∨ x = fun _ => 1 := by
  decide +kernel

theorem act_crd (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    act σ (crd x) = crd fun i => x (σ⁻¹ i) := by
  have e : ∃ c : ZMod 2, (fun i => sec (crd x) (σ⁻¹ i)) = (fun i => x (σ⁻¹ i)) + fun _ => c := by
    rcases sec_crd_aux x with h | h
    · exact ⟨0, funext fun i => by rw [h]; simp⟩
    · exact ⟨1, funext fun i => by rw [h]; rfl⟩
  obtain ⟨c, hc⟩ := e
  show crd (fun i => sec (crd x) (σ⁻¹ i)) = _
  rw [hc, crd_add, crd_const, add_zero]

theorem act_mul (σ τ : Equiv.Perm (Fin 6)) (v : Vec5) : act (σ * τ) v = act σ (act τ v) := by
  show crd (fun i => sec v ((σ * τ)⁻¹ i)) = act σ (crd fun i => sec v (τ⁻¹ i))
  rw [act_crd, mul_inv_rev]
  rfl

theorem act_one (v : Vec5) : act 1 v = v := by
  show crd (fun i => sec v ((1 : Equiv.Perm (Fin 6))⁻¹ i)) = v
  rw [inv_one]
  exact crd_sec v

@[expose] def actHom : Equiv.Perm (Fin 6) →* Equiv.Perm Vec5 where
  toFun σ :=
    { toFun := act σ
      invFun := act σ⁻¹
      left_inv := fun v => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun v => by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := Equiv.ext act_one
  map_mul' σ τ := Equiv.ext fun v => act_mul σ τ v

theorem actHom_apply (σ : Equiv.Perm (Fin 6)) (v : Vec5) : actHom σ v = act σ v := rfl

theorem crd_single_inj : ∀ a b : Fin 6, crd (Pi.single a 1) = crd (Pi.single b 1) → a = b := by
  decide +kernel

theorem act_single (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    act σ (crd (Pi.single i 1)) = crd (Pi.single (σ i) 1) := by
  rw [act_crd]
  congr 1
  funext k
  simp only [Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem eq_one_of_act {σ : Equiv.Perm (Fin 6)} (h : ∀ v, act σ v = v) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  have h1 := h (crd (Pi.single i 1))
  rw [act_single] at h1
  exact crd_single_inj _ _ h1

end CFSG.Quasithin.H13.P5
