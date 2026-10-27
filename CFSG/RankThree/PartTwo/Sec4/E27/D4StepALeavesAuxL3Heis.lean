module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix

section Line

variable {E : Type*} [Field E]

theorem heis_no_line {A B : Matrix (Fin 3) (Fin 3) E} {c : E} (hA : IsUnit A) (hB : IsUnit B)
    (hc : c ≠ 1) (hBA : B * A = c • (A * B)) (U : Submodule E (Fin 3 → E))
    (hU : Module.finrank E U = 1) (hAU : ∀ u ∈ U, A *ᵥ u ∈ U) (hBU : ∀ u ∈ U, B *ᵥ u ∈ U) :
    False := by
  classical
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hU
  have hu0 : (v : Fin 3 → E) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨a, ha⟩ := hv ⟨A *ᵥ (v : Fin 3 → E), hAU _ v.2⟩
  obtain ⟨b, hb⟩ := hv ⟨B *ᵥ (v : Fin 3 → E), hBU _ v.2⟩
  have ha' : A *ᵥ (v : Fin 3 → E) = a • (v : Fin 3 → E) := (congrArg Subtype.val ha).symm
  have hb' : B *ᵥ (v : Fin 3 → E) = b • (v : Fin 3 → E) := (congrArg Subtype.val hb).symm
  have h1 : (B * A) *ᵥ (v : Fin 3 → E) = (a * b) • (v : Fin 3 → E) := by
    rw [← Matrix.mulVec_mulVec, ha', Matrix.mulVec_smul, hb', smul_smul, mul_comm]
  have h2 : (A * B) *ᵥ (v : Fin 3 → E) = (a * b) • (v : Fin 3 → E) := by
    rw [← Matrix.mulVec_mulVec, hb', Matrix.mulVec_smul, ha', smul_smul, mul_comm]
  have h3 : (B * A) *ᵥ (v : Fin 3 → E) = c • ((A * B) *ᵥ (v : Fin 3 → E)) := by
    rw [hBA, Matrix.smul_mulVec]
  rw [h1, h2] at h3
  have h4 : ((1 - c) * (a * b)) • (v : Fin 3 → E) = 0 := by
    have h4' : ((1 - c) * (a * b)) • (v : Fin 3 → E) =
        (a * b) • (v : Fin 3 → E) - c • ((a * b) • (v : Fin 3 → E)) := by
      rw [sub_mul, one_mul, sub_smul, mul_smul c (a * b)]
    rw [h4', ← h3, sub_self]
  have h5 : (1 - c) * (a * b) = 0 := by
    rcases smul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd h hu0
  have hdA : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det A |>.mp hA).ne_zero
  have hdB : B.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det B |>.mp hB).ne_zero
  rcases mul_eq_zero.mp h5 with h | h
  · exact hc (sub_eq_zero.mp h).symm
  · rcases mul_eq_zero.mp h with h | h
    · apply hu0
      apply Matrix.eq_zero_of_mulVec_eq_zero hdA
      rw [ha', h, zero_smul]
    · apply hu0
      apply Matrix.eq_zero_of_mulVec_eq_zero hdB
      rw [hb', h, zero_smul]

end Line

section Alg

variable {E : Type*} [Field E] [IsAlgClosed E]

theorem heis_scalar_alg {A B g : Matrix (Fin 3) (Fin 3) E} {c : E} (hA : IsUnit A) (hB : IsUnit B)
    (hc : c ≠ 1) (hBA : B * A = c • (A * B)) (hgA : g * A = A * g) (hgB : g * B = B * g) :
    ∃ r : E, g = Matrix.scalar (Fin 3) r := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hgv : g *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  set N : Matrix (Fin 3) (Fin 3) E := g - μ • (1 : Matrix (Fin 3) (Fin 3) E) with hN
  have hNA : N * A = A * N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, hgA, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hNB : N * B = B * N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, hgB, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hNv : N *ᵥ v = 0 := by
    rw [hN, Matrix.sub_mulVec, hgv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  by_cases hN0 : N = 0
  · refine ⟨μ, ?_⟩
    have : g = μ • (1 : Matrix (Fin 3) (Fin 3) E) := by
      rw [hN] at hN0
      exact sub_eq_zero.mp hN0
    rw [this, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  exfalso
  set T : (Fin 3 → E) →ₗ[E] (Fin 3 → E) := Matrix.toLin' N with hT
  have hTap : ∀ w, T w = N *ᵥ w := fun w => Matrix.toLin'_apply N w
  have hT0 : T ≠ 0 := fun h => hN0 (Matrix.toLin'.injective (by rw [← hT, h, map_zero]))
  have hsum : Module.finrank E (LinearMap.range T) + Module.finrank E (LinearMap.ker T) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker T
    simpa using this
  have hKne : LinearMap.ker T ≠ ⊥ := by
    intro h
    apply hv0
    have : v ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, hTap, hNv]
    rw [h] at this
    exact (Submodule.mem_bot E).mp this
  have hRne : LinearMap.range T ≠ ⊥ := by
    intro h
    apply hT0
    refine LinearMap.ext fun w => ?_
    have hmem : T w ∈ LinearMap.range T := LinearMap.mem_range_self T w
    rw [h] at hmem
    exact (Submodule.mem_bot E).mp hmem
  have hK1 : 1 ≤ Module.finrank E (LinearMap.ker T) := Submodule.one_le_finrank_iff.mpr hKne
  have hR1 : 1 ≤ Module.finrank E (LinearMap.range T) := Submodule.one_le_finrank_iff.mpr hRne
  have hKinv : ∀ (M : Matrix (Fin 3) (Fin 3) E), N * M = M * N →
      ∀ u ∈ LinearMap.ker T, M *ᵥ u ∈ LinearMap.ker T := by
    intro M hM u hu
    rw [LinearMap.mem_ker, hTap] at hu ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have hRinv : ∀ (M : Matrix (Fin 3) (Fin 3) E), N * M = M * N →
      ∀ u ∈ LinearMap.range T, M *ᵥ u ∈ LinearMap.range T := by
    intro M hM u hu
    obtain ⟨w, rfl⟩ := hu
    refine ⟨M *ᵥ w, ?_⟩
    rw [hTap, hTap, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec]
  by_cases hk : Module.finrank E (LinearMap.ker T) = 1
  · exact heis_no_line hA hB hc hBA (LinearMap.ker T) hk (hKinv A hNA) (hKinv B hNB)
  · have hr : Module.finrank E (LinearMap.range T) = 1 := by omega
    exact heis_no_line hA hB hc hBA (LinearMap.range T) hr (hRinv A hNA) (hRinv B hNB)

end Alg

section AnyField

variable {F : Type*} [Field F]

theorem heis_scalar {A B g : Matrix (Fin 3) (Fin 3) F} {c : F} (hA : IsUnit A) (hB : IsUnit B)
    (hc : c ≠ 1) (hBA : B * A = c • (A * B)) (hgA : g * A = A * g) (hgB : g * B = B * g) :
    ∃ r : F, g = Matrix.scalar (Fin 3) r := by
  classical
  let E := AlgebraicClosure F
  let φ : F →+* E := algebraMap F E
  have hφ : Function.Injective φ := (algebraMap F E).injective
  have hmul : ∀ M N : Matrix (Fin 3) (Fin 3) F, (M * N).map φ = M.map φ * N.map φ :=
    fun M N => Matrix.map_mul
  have hsm : ∀ (r : F) (M : Matrix (Fin 3) (Fin 3) F), (r • M).map φ = φ r • M.map φ :=
    fun r M => by ext i j; simp
  have hA' : IsUnit (A.map φ) := by
    have := (RingHom.isUnit_map (φ.mapMatrix (m := Fin 3)) hA)
    exact this
  have hB' : IsUnit (B.map φ) := by
    have := (RingHom.isUnit_map (φ.mapMatrix (m := Fin 3)) hB)
    exact this
  have hc' : φ c ≠ 1 := fun h => hc (hφ (by rw [h, map_one]))
  have hBA' : B.map φ * A.map φ = φ c • (A.map φ * B.map φ) := by
    rw [← hmul, ← hmul, ← hsm, hBA]
  have hgA' : g.map φ * A.map φ = A.map φ * g.map φ := by
    rw [← hmul, ← hmul, hgA]
  have hgB' : g.map φ * B.map φ = B.map φ * g.map φ := by
    rw [← hmul, ← hmul, hgB]
  obtain ⟨r, hr⟩ := heis_scalar_alg hA' hB' hc' hBA' hgA' hgB'
  refine ⟨g 0 0, ?_⟩
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at hij
  have h00 := congrFun (congrFun hr 0) 0
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, if_true] at h00
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij' : i = j
  · subst hij'
    simp only [if_true] at hij ⊢
    exact hφ (hij.trans h00.symm)
  · simp only [hij', if_false] at hij ⊢
    exact hφ (by rw [hij, map_zero])

end AnyField

end CFSG.RankThree.PartTwo.Sec4.E27
