module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import CFSG.Quasithin.Vol2.Ch6SL2Aut

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem exists_mulAut_of_normalizes {L Q : Subgroup G} {F : Type*} [Field F]
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) {d : G}
    (hdL : d ∈ Subgroup.normalizer (L : Set G)) (hdQ : d ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ θ : MulAut SL(2, F), ∀ x y : ↥L, (y : G) = d * x * d⁻¹ → θ (α x) = α y := by
  classical
  let κ : MulAut ↥L := L.normalizerMonoidHom ⟨d, hdL⟩
  have hκ : ∀ x : ↥L, ((κ x : ↥L) : G) = d * x * d⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨d, hdL⟩ x
  let ψ : ↥L →* SL(2, F) := α.comp κ.toMonoidHom
  have hψ : Function.Surjective ψ := hα.comp κ.surjective
  have hkerEq : α.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change α x = 1 ↔ α (κ x) = 1
    rw [hker, hker, hκ]
    exact Subgroup.mem_normalizer_iff.mp hdQ x
  let e1 := QuotientGroup.quotientKerEquivOfSurjective α hα
  let e2 := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let e := QuotientGroup.quotientMulEquivOfEq hkerEq
  refine ⟨e1.symm.trans (e.trans e2), fun x y hy => ?_⟩
  have hyx : y = κ x := Subtype.ext (by rw [hκ]; exact hy)
  have h1 : e1.symm (α x) = (x : ↥L ⧸ α.ker) := by
    apply e1.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, hyx]
  rfl

private def uSL' {F : Type*} [Field F] (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem exists_conj_of_unitriangular {F : Type} [Field F] [Finite F] [CharP F 2]
    (θ : MulAut SL(2, F)) {ν : F} (hν : ν ≠ 0)
    (h : ∀ (B : SL(2, F)) (s : F), (B : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] →
      ((θ B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, ν * s; 0, 1]) :
    ∃ P : SL(2, F), ∀ B : SL(2, F), θ B = P * B * P⁻¹ := by
  classical
  obtain ⟨M, σ, hM⟩ := CFSG.Quasithin.H13.exists_conj_map_of_mulAut_ch6 θ
  have hMM : ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (M : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  generalize (M : Matrix (Fin 2) (Fin 2) F) = Mm at hM hMM hdet
  generalize ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Mi at hM hMM
  have key : ∀ s : F, Mm * !![1, σ s; 0, 1] = !![1, ν * s; 0, 1] * Mm := by
    intro s
    have h1 := hM (uSL' s)
    rw [h (uSL' s) s rfl] at h1
    have hmap : ((uSL' s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ = !![1, σ s; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uSL']
    rw [hmap] at h1
    rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, hMM, Matrix.mul_one]
  have e00 := congrFun (congrFun (key 1) 0) 0
  have e01 : ∀ s : F, Mm 0 0 * σ s = ν * s * Mm 1 1 := by
    intro s
    have h0 := congrFun (congrFun (key s) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h0
    linear_combination h0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e00
  have hm10 : Mm 1 0 = 0 := by
    rcases e00 with h0 | h0
    · exact absurd h0 hν
    · exact h0
  have hm00 : Mm 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_two, h0, hm10]
    ring
  have hσ : ∀ s : F, σ s = s := by
    intro s
    have h1 := e01 1
    simp only [map_one, mul_one] at h1
    have h2 := e01 s
    apply mul_left_cancel₀ hm00
    rw [h2, h1]
    ring
  have hconj : ∀ B : SL(2, F), ((θ B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Mm * (B : Matrix (Fin 2) (Fin 2) F) * Mi := by
    intro B
    rw [hM B]
    congr 2
    ext i j
    simp [hσ]
  obtain ⟨δ, hδ⟩ := isSquare_of_charTwo' Mm.det
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [hδ, mul_zero])
  let P : SL(2, F) := ⟨δ⁻¹ • Mm, by
    rw [Matrix.det_smul, Fintype.card_fin, hδ]
    field_simp⟩
  refine ⟨P, fun B => ?_⟩
  apply eq_mul_inv_of_mul_eq
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hconj]
  change Mm * (B : Matrix (Fin 2) (Fin 2) F) * Mi * (δ⁻¹ • Mm) =
    (δ⁻¹ • Mm) * (B : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc _ Mi, hMM, Matrix.mul_one]

theorem exists_inner_of_unitriangular {L Q : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) {d : G}
    (hdL : d ∈ Subgroup.normalizer (L : Set G)) (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    {ν : F} (hν : ν ≠ 0)
    (h : ∀ s : F, ∃ x y : ↥L, (y : G) = d * x * d⁻¹ ∧
      (α x : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] ∧
      (α y : Matrix (Fin 2) (Fin 2) F) = !![1, ν * s; 0, 1]) :
    ∃ g ∈ L, ∀ x ∈ L, d * x * d⁻¹ * (g * x * g⁻¹)⁻¹ ∈ Q := by
  obtain ⟨θ, hθ⟩ := exists_mulAut_of_normalizes α hα hker hdL hdQ
  have hU : ∀ (B : SL(2, F)) (s : F), (B : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] →
      ((θ B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, ν * s; 0, 1] := by
    intro B s hB
    obtain ⟨x, y, hy, hx, hyα⟩ := h s
    have hBx : B = α x := Subtype.ext (by rw [hB, hx])
    rw [hBx, hθ x y hy, hyα]
  obtain ⟨P, hP⟩ := exists_conj_of_unitriangular θ hν hU
  obtain ⟨g, hg⟩ := hα P
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hdx : d * x * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hdL x).mp hx
  have hY := hθ ⟨x, hx⟩ ⟨d * x * d⁻¹, hdx⟩ rfl
  rw [hP, ← hg] at hY
  have h1 : α (⟨d * x * d⁻¹, hdx⟩ * (g * ⟨x, hx⟩ * g⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hY]
    group
  exact (hker _).mp h1

end CFSG.Quasithin.F112R.St84

end
