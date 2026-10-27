module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def VanishesOn (S0 : Finset (Fin 8)) (v : Fin 8 → ZMod 3) : Prop := ∀ i ∈ S0, v i = 0

private lemma p9uN7DG_inv_mul_comm {M : Type*} [Monoid M] {a b c : M} (hab : a * b = b * a)
    (hbc : b * c = 1) (hcb : c * b = 1) : c * a = a * c := by
  have hinner : a * (b * c) = b * (a * c) := by rw [← mul_assoc, hab, mul_assoc]
  calc c * a = c * (a * (b * c)) := by rw [hbc, mul_one]
    _ = c * (b * (a * c)) := by rw [hinner]
    _ = a * c := by rw [← mul_assoc, hcb, one_mul]

private lemma p9uN7DG_neg_eq_self (a : ZMod 3) (h : -a = a) : a = 0 := by
  revert h
  revert a
  decide

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

@[expose] def dentD (S0 : Finset (Fin 8)) : Subgroup X where
  carrier := {x | S.ρ x * sgn S0 = sgn S0 * S.ρ x}
  mul_mem' {a b} ha hb := by
    show S.ρ (a * b) * sgn S0 = sgn S0 * S.ρ (a * b)
    have ha' : S.ρ a * sgn S0 = sgn S0 * S.ρ a := ha
    have hb' : S.ρ b * sgn S0 = sgn S0 * S.ρ b := hb
    rw [map_mul]
    calc S.ρ a * S.ρ b * sgn S0
        = S.ρ a * (S.ρ b * sgn S0) := by rw [Matrix.mul_assoc]
      _ = S.ρ a * (sgn S0 * S.ρ b) := by rw [hb']
      _ = S.ρ a * sgn S0 * S.ρ b := by rw [← Matrix.mul_assoc]
      _ = sgn S0 * S.ρ a * S.ρ b := by rw [ha']
      _ = sgn S0 * (S.ρ a * S.ρ b) := by rw [Matrix.mul_assoc]
  one_mem' := by
    show S.ρ 1 * sgn S0 = sgn S0 * S.ρ 1
    rw [map_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {x} hx := by
    show S.ρ x⁻¹ * sgn S0 = sgn S0 * S.ρ x⁻¹
    have hx' : S.ρ x * sgn S0 = sgn S0 * S.ρ x := hx
    exact p9uN7DG_inv_mul_comm hx'.symm
      (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one])

@[expose] def dentQ (S0 : Finset (Fin 8)) : Subgroup X where
  carrier := {x | ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x *ᵥ v = v}
  mul_mem' {x y} hx hy := by
    have hx' : ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x *ᵥ v = v := hx
    have hy' : ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ y *ᵥ v = v := hy
    show ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ (x * y) *ᵥ v = v
    intro v hv
    rw [map_mul, ← Matrix.mulVec_mulVec, hy' v hv, hx' v hv]
  one_mem' := by
    show ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ 1 *ᵥ v = v
    intro v _
    rw [map_one, Matrix.one_mulVec]
  inv_mem' {x} hx := by
    have hx' : ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x *ᵥ v = v := hx
    show ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x⁻¹ *ᵥ v = v
    intro v hv
    calc S.ρ x⁻¹ *ᵥ v = S.ρ x⁻¹ *ᵥ (S.ρ x *ᵥ v) := by rw [hx' v hv]
      _ = (S.ρ x⁻¹ * S.ρ x) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

@[expose] def dentF2 (S0 : Finset (Fin 8)) : Subgroup X := S.F1 ⊓ S.dentQ S0

theorem mem_dentD_iff {S0 : Finset (Fin 8)} {x : X} :
    x ∈ S.dentD S0 ↔ S.ρ x * sgn S0 = sgn S0 * S.ρ x :=
  Iff.rfl

theorem mem_dentQ_iff {S0 : Finset (Fin 8)} {x : X} :
    x ∈ S.dentQ S0 ↔ ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x *ᵥ v = v :=
  Iff.rfl

theorem mem_dentD_iff_comm {S0 : Finset (Fin 8)} {τ : X} (hτ : S.ρ τ = sgn S0) {x : X} :
    x ∈ S.dentD S0 ↔ x * τ = τ * x := by
  rw [mem_dentD_iff, ← hτ, ← map_mul, ← map_mul]
  exact ⟨fun h => S.ρ_inj h, fun h => congrArg S.ρ h⟩

theorem vanishesOn_iff_sgn_mulVec {S0 : Finset (Fin 8)} {v : Fin 8 → ZMod 3} :
    VanishesOn S0 v ↔ sgn S0 *ᵥ v = v := by
  rw [q2nN7_sgn_mulVec]
  constructor
  · intro h
    funext i
    by_cases hi : i ∈ S0
    · rw [if_pos hi, h i hi]
      exact neg_zero
    · simp [hi]
  · intro h i hi
    have h' := congrFun h i
    simp [hi] at h'
    exact p9uN7DG_neg_eq_self (v i) h'

theorem vanishesOn_mulVec_of_mem_dentD {S0 : Finset (Fin 8)} {d : X} (hd : d ∈ S.dentD S0)
    {v : Fin 8 → ZMod 3} (hv : VanishesOn S0 v) : VanishesOn S0 (S.ρ d *ᵥ v) := by
  rw [vanishesOn_iff_sgn_mulVec] at hv ⊢
  have hd' : S.ρ d * sgn S0 = sgn S0 * S.ρ d := hd
  calc sgn S0 *ᵥ (S.ρ d *ᵥ v) = (sgn S0 * S.ρ d) *ᵥ v := by rw [Matrix.mulVec_mulVec]
    _ = (S.ρ d * sgn S0) *ᵥ v := by rw [← hd']
    _ = S.ρ d *ᵥ (sgn S0 *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = S.ρ d *ᵥ v := by rw [hv]

theorem dentQ_le_H {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0) : S.dentQ S0 ≤ S.H := by
  intro x hx
  have hx' : ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ x *ᵥ v = v := hx
  show S.ρ x *ᵥ e0 = e0
  exact hx' e0 (by
    intro i hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
    show Pi.single 0 1 i = 0
    exact Pi.single_eq_of_ne hi0 1)

theorem dentQ_conj_mem {S0 : Finset (Fin 8)} {d : X} (hd : d ∈ S.dentD S0) {q : X}
    (hq : q ∈ S.dentQ S0) : d * q * d⁻¹ ∈ S.dentQ S0 := by
  have hd_inv : d⁻¹ ∈ S.dentD S0 := (S.dentD S0).inv_mem hd
  have hq' : ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ q *ᵥ v = v := hq
  show ∀ v : Fin 8 → ZMod 3, VanishesOn S0 v → S.ρ (d * q * d⁻¹) *ᵥ v = v
  intro v hv
  have hdv : VanishesOn S0 (S.ρ d⁻¹ *ᵥ v) :=
    vanishesOn_mulVec_of_mem_dentD S hd_inv hv
  have hqw : S.ρ q *ᵥ (S.ρ d⁻¹ *ᵥ v) = S.ρ d⁻¹ *ᵥ v := hq' _ hdv
  calc S.ρ (d * q * d⁻¹) *ᵥ v
      = S.ρ d *ᵥ (S.ρ q *ᵥ (S.ρ d⁻¹ *ᵥ v)) := by
        rw [map_mul, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = S.ρ d *ᵥ (S.ρ d⁻¹ *ᵥ v) := by rw [hqw]
    _ = v := by
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem dentQ_conj_dentF2 {S0 : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S0) {q : X}
    (hq : q ∈ S.dentQ S0) {f : X} (hf : f ∈ S.dentF2 S0) : q * f * q⁻¹ ∈ S.dentF2 S0 := by
  have hqH : q ∈ S.H := dentQ_le_H S h0 hq
  simp only [dentF2, Subgroup.mem_inf] at hf ⊢
  exact ⟨conj_mem_F1 S hqH hf.1,
    (S.dentQ S0).mul_mem ((S.dentQ S0).mul_mem hq hf.2) ((S.dentQ S0).inv_mem hq)⟩

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
