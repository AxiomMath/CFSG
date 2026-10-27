module

public import CFSG.Quasithin.Background.F7TwoInvL3Cong
public import CFSG.Quasithin.Background.F7TwoInvL3Unip

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false in
theorem antiSupp_of_mul_eq_one {A B : Matrix (Fin 3) (Fin 3) K} (hA : AntiSupp A)
    (hAB : A * B = 1) : AntiSupp B := by
  obtain ⟨a00, a01, a10, a12, a21, a22⟩ := hA
  have e00 := congrFun (congrFun hAB 0) 0
  have e01 := congrFun (congrFun hAB 0) 1
  have e02 := congrFun (congrFun hAB 0) 2
  have e10 := congrFun (congrFun hAB 1) 0
  have e11 := congrFun (congrFun hAB 1) 1
  have e12 := congrFun (congrFun hAB 1) 2
  have e20 := congrFun (congrFun hAB 2) 0
  have e21 := congrFun (congrFun hAB 2) 1
  have e22 := congrFun (congrFun hAB 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a12] at e00 e01 e02 e10
  simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a12, a21, a22] at e11 e12 e20 e21 e22
  have h02 : A 0 2 ≠ 0 := fun h => by rw [h, zero_mul] at e00; exact zero_ne_one e00
  have h11 : A 1 1 ≠ 0 := fun h => by rw [h, zero_mul] at e11; exact zero_ne_one e11
  have h20 : A 2 0 ≠ 0 := fun h => by rw [h, zero_mul] at e22; exact zero_ne_one e22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e20.resolve_left h20
  · exact e21.resolve_left h20
  · exact e10.resolve_left h11
  · exact e12.resolve_left h11
  · exact e01.resolve_left h02
  · exact e02.resolve_left h02

set_option linter.unusedSimpArgs false in
theorem antiSupp_diag_entries {A B : Matrix (Fin 3) (Fin 3) K} (hA : AntiSupp A)
    (hAB : A * B = 1) : A 0 2 * B 2 0 = 1 ∧ A 1 1 * B 1 1 = 1 ∧ A 2 0 * B 0 2 = 1 := by
  obtain ⟨a00, a01, a10, a12, a21, a22⟩ := hA
  have e00 := congrFun (congrFun hAB 0) 0
  have e11 := congrFun (congrFun hAB 1) 1
  have e22 := congrFun (congrFun hAB 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01] at e00
  simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a12] at e11
  simp [Matrix.mul_apply, Fin.sum_univ_three, a21, a22] at e22
  exact ⟨e00, e11, e22⟩

set_option linter.unusedSimpArgs false in
theorem antidiag_conj_mem_unitriangular {A B : Matrix (Fin 3) (Fin 3) K} (hA : AntiSupp A)
    (hAB : A * B = 1) {y : Matrix (Fin 3) (Fin 3) K}
    (hy : y 0 1 = 0 ∧ y 0 2 = 0 ∧ y 1 2 = 0 ∧ y 0 0 = 1 ∧ y 1 1 = 1 ∧ y 2 2 = 1)
    {v : SpecialLinearGroup (Fin 3) K} (hv : (v : Matrix (Fin 3) (Fin 3) K) = A * y * B) :
    v ∈ unitriangular 3 K := by
  have hB := antiSupp_of_mul_eq_one hA hAB
  obtain ⟨d0, d1, d2⟩ := antiSupp_diag_entries hA hAB
  obtain ⟨a00, a01, a10, a12, a21, a22⟩ := hA
  obtain ⟨b00, b01, b10, b12, b21, b22⟩ := hB
  obtain ⟨y01, y02, y12, y00, y11, y22⟩ := hy
  rw [mem_unitriangular]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [hv]
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hji; decide)
        | simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a12, a21, a22, b00, b01,
            b10, b12, b21, b22, y01, y02, y12, y00, y11, y22]
  · rw [hv]
    fin_cases i <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a12, a21, a22, b00, b01,
        b10, b12, b21, b22, y01, y02, y12, y00, y11, y22, d0, d1, d2]

set_option linter.unusedSimpArgs false in
theorem antidiag_conj_mem_lowerUnitriangular {A B : Matrix (Fin 3) (Fin 3) K} (hA : AntiSupp A)
    (hAB : A * B = 1) {y : Matrix (Fin 3) (Fin 3) K}
    (hy : y 1 0 = 0 ∧ y 2 0 = 0 ∧ y 2 1 = 0 ∧ y 0 0 = 1 ∧ y 1 1 = 1 ∧ y 2 2 = 1)
    {v : SpecialLinearGroup (Fin 3) K} (hv : (v : Matrix (Fin 3) (Fin 3) K) = A * y * B) :
    v ∈ lowerUnitriangular 3 K := by
  have hB := antiSupp_of_mul_eq_one hA hAB
  obtain ⟨d0, d1, d2⟩ := antiSupp_diag_entries hA hAB
  obtain ⟨a00, a01, a10, a12, a21, a22⟩ := hA
  obtain ⟨b00, b01, b10, b12, b21, b22⟩ := hB
  obtain ⟨y10, y20, y21, y00, y11, y22⟩ := hy
  rw [mem_lowerUnitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hv]
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hij; decide)
        | simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a12, a21, a22, b00, b01,
            b10, b12, b21, b22, y10, y20, y21, y00, y11, y22]
  · rw [hv]
    fin_cases i <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a12, a21, a22, b00, b01,
        b10, b12, b21, b22, y10, y20, y21, y00, y11, y22, d0, d1, d2]

theorem invAutGen_of_graph_lift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*} [Group X]
    [Finite X] (hs : IsSimpleGroup X) (hnonab : ∃ x y : X, x * y ≠ y * x)
    (θ : SpecialLinearGroup (Fin 3) (ZMod p) →* X) (hθ : Function.Surjective θ) {φ : MulAut X}
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (α : SpecialLinearGroup (Fin 3) (ZMod p) → SpecialLinearGroup (Fin 3) (ZMod p))
    (hα : ∀ x, φ (θ x) = θ (α x)) (hαα : ∀ x, α (α x) = x)
    (A B : Matrix (Fin 3) (Fin 3) (ZMod p)) (hAB : A * B = 1) (hBA : B * A = 1)
    (hαm : ∀ x, ((α x : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      A * (((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ * B) : InvAutGen X φ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have hsymm := symm_of_graph_lift h2 A B hAB hBA α hαm hαα
  have hdetA : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  obtain ⟨Q, hQ⟩ := exists_sl_antidiag_of_isotropic h2 A hsymm hdetA (exists_isotropic_zmod A)
  set ψ : MulAut X := MulAut.conj (θ Q) with hψ
  have hφ'2 : (ψ * φ * ψ⁻¹) * (ψ * φ * ψ⁻¹) = 1 := by
    calc (ψ * φ * ψ⁻¹) * (ψ * φ * ψ⁻¹) = ψ * (φ * φ) * ψ⁻¹ := by group
      _ = 1 := by rw [hφ2]; group
  have hφ'1 : ψ * φ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hφ1
    calc φ = ψ⁻¹ * (ψ * φ * ψ⁻¹) * ψ := by group
      _ = 1 := by rw [h]; group
  refine (InvAutGen.conj_iff ψ φ).mpr ?_
  have hθQ : (θ Q)⁻¹ = θ Q⁻¹ := (map_inv θ Q).symm
  have hψ1 : ∀ y : SpecialLinearGroup (Fin 3) (ZMod p), ψ (θ y) = θ (Q * y * Q⁻¹) := by
    intro y
    rw [hψ, MulAut.conj_apply, hθQ, map_mul, map_mul]
  have hψ2 : ∀ y : SpecialLinearGroup (Fin 3) (ZMod p), ψ⁻¹ (θ y) = θ (Q⁻¹ * y * Q) := by
    intro y
    have h : ψ⁻¹ = ψ.symm := rfl
    rw [h, hψ, MulAut.conj_symm_apply, hθQ, map_mul, map_mul]
  have hQinv : (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 :=
    congrArg (fun g : SpecialLinearGroup (Fin 3) (ZMod p) =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))) (mul_inv_cancel Q)
  have hinvQ : ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 :=
    congrArg (fun g : SpecialLinearGroup (Fin 3) (ZMod p) =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))) (inv_mul_cancel Q)
  set A' : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) * A * (Q : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ with hA'
  set B' : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * B *
      ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hB'
  have hA'B' : A' * B' = 1 := by
    have h1 : (Q : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
        ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hinvQ, Matrix.transpose_one]
    calc A' * B' = (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) * (A *
          ((Q : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
            ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ) *
          B) * ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
          simp only [hA', hB', Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hAB, Matrix.mul_one, hQinv]
  have hv : ∀ x : SpecialLinearGroup (Fin 3) (ZMod p),
      ((Q * α (Q⁻¹ * x * Q) * Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) =
        A' * (((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ * B' := by
    intro x
    have e : (Q⁻¹ * x * Q)⁻¹ = Q⁻¹ * x⁻¹ * Q := by group
    show (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      ((α (Q⁻¹ * x * Q) : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = _
    rw [hαm, e]
    show (Q : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      (A * (((Q⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (Q : Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ * B) * _ = _
    simp only [hA', hB', Matrix.transpose_mul, Matrix.mul_assoc]
  refine invAutGen_of_unitriangular_invariant hodd hs hnonab θ hθ hφ'2 hφ'1
    (fun x => Q * α (Q⁻¹ * x * Q) * Q⁻¹) (fun x => ?_) (fun u hu => ?_) (fun u hu => ?_)
  · rw [MulAut.mul_apply, MulAut.mul_apply, hψ2, hα, hψ1]
  · have hui := mem_unitriangular.mp (inv_mem hu)
    refine antidiag_conj_mem_unitriangular hQ hA'B' ?_ (hv u)
    simp only [Matrix.transpose_apply]
    exact ⟨hui.1 1 0 (by decide), hui.1 2 0 (by decide), hui.1 2 1 (by decide), hui.2 0,
      hui.2 1, hui.2 2⟩
  · have hui := mem_lowerUnitriangular.mp (inv_mem hu)
    refine antidiag_conj_mem_lowerUnitriangular hQ hA'B' ?_ (hv u)
    simp only [Matrix.transpose_apply]
    exact ⟨hui.1 0 1 (by decide), hui.1 0 2 (by decide), hui.1 1 2 (by decide), hui.2 0,
      hui.2 1, hui.2 2⟩

end CFSG.Quasithin.F7Two
