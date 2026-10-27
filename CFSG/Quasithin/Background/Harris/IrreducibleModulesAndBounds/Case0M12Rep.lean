module

public import CFSG.Quasithin.Background.SmithB45MatM12Rep
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12SelfDual

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12
  CFSG.Sporadic.Mathieu CFSG.Blueprint Matrix

namespace Case0M12

@[expose] def m12M : Matrix (Fin 10) (Fin 12) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0; 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0; 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0]

@[expose] def m12N : Matrix (Fin 12) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 1, 1, 1, 1; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 1, 1, 1, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 1, 0, 1]

@[expose] def rA : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 1, 1, 1, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 1, 1, 1; 1, 1, 0, 1, 0, 1, 1, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 1, 1, 1, 1, 0, 0; 1, 1, 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 1, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 1, 0, 1, 0]

@[expose] def rB : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0, 1, 1; 1, 0, 0, 0, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 0, 1, 1, 0, 1; 1, 0, 1, 0, 1, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 1, 0, 1, 1; 0, 1, 1, 1, 0, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0, 1, 0]

theorem rA_eq : maskMat 10 10 (cols10 arrA) = rA := by decide +kernel

theorem rB_eq : maskMat 10 10 (cols10 arrB) = rB := by decide +kernel

@[expose] def spanVec (i : Fin 12) : Fin 12 → ZMod 2 := Pi.single 0 1 + Pi.single i 1

theorem eq_sum_spanVec {u : Fin 12 → ZMod 2} (hu : ∑ i, u i = 0) :
    u = ∑ i, u i • spanVec i := by
  funext j
  simp only [spanVec, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hj : j = 0 <;> simp [hj, hu]

theorem linear_eq_of_spanVec {X : Type*} [AddCommMonoid X] [Module (ZMod 2) X]
    (T₁ T₂ : (Fin 12 → ZMod 2) →ₗ[ZMod 2] X) (h : ∀ i, T₁ (spanVec i) = T₂ (spanVec i))
    {u : Fin 12 → ZMod 2} (hu : ∑ i, u i = 0) : T₁ u = T₂ u := by
  have h1 := eq_sum_spanVec hu
  calc T₁ u = T₁ (∑ i, u i • spanVec i) := by rw [← h1]
    _ = T₂ (∑ i, u i • spanVec i) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, h i]
    _ = T₂ u := by rw [← h1]

@[expose] def permActL (σ : Equiv.Perm (Fin 12)) :
    (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (σ⁻¹ : Equiv.Perm (Fin 12))

theorem permActL_apply (σ : Equiv.Perm (Fin 12)) (u : Fin 12 → ZMod 2) :
    permActL σ u = permAct σ u := rfl

theorem equivariant_of_spanVec (σ : Equiv.Perm (Fin 12)) (R : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ i, m12M *ᵥ permAct σ (spanVec i) = R *ᵥ (m12M *ᵥ spanVec i)) {u : Fin 12 → ZMod 2}
    (hu : ∑ i, u i = 0) : m12M *ᵥ permAct σ u = R *ᵥ (m12M *ᵥ u) := by
  have := linear_eq_of_spanVec (Matrix.mulVecLin m12M ∘ₗ permActL σ)
    (Matrix.mulVecLin R ∘ₗ Matrix.mulVecLin m12M) (fun i => by
      simpa [permActL_apply] using h i) hu
  simpa [permActL_apply] using this

theorem equivariant_A : ∀ i, m12M *ᵥ permAct m12gA (spanVec i) = rA *ᵥ (m12M *ᵥ spanVec i) := by
  decide +kernel

theorem equivariant_B : ∀ i, m12M *ᵥ permAct m12gB (spanVec i) = rB *ᵥ (m12M *ᵥ spanVec i) := by
  decide +kernel

theorem permAct_mul (σ τ : Equiv.Perm (Fin 12)) (u : Fin 12 → ZMod 2) :
    permAct (σ * τ) u = permAct σ (permAct τ u) := by
  funext i
  simp [permAct, _root_.mul_inv_rev]

theorem permAct_one (u : Fin 12 → ZMod 2) : permAct (1 : Equiv.Perm (Fin 12)) u = u := by
  funext i
  simp [permAct]

theorem equivariant
    (g : G12)
    {u : Fin 12 → ZMod 2} (hu : ∑ i, u i = 0) :
    m12M *ᵥ permAct (g : Equiv.Perm (Fin 12)) u = rep10 g *ᵥ (m12M *ᵥ u) := by
  have key : ∀ g : G12, ∀ u : Fin 12 → ZMod 2, ∑ i, u i = 0 →
      m12M *ᵥ permAct (g : Equiv.Perm (Fin 12)) u = rep10 g *ᵥ (m12M *ᵥ u) := by
    refine forall_of_closure (G := G12) closure_m12ab
      (fun g => ∀ u : Fin 12 → ZMod 2, ∑ i, u i = 0 →
        m12M *ᵥ permAct (g : Equiv.Perm (Fin 12)) u = rep10 g *ᵥ (m12M *ᵥ u)) ?_ ?_ ?_
    · intro u _
      simp [permAct_one]
    · rintro s (rfl | rfl)
      · intro u hu
        rw [rep10_m12a, rA_eq]
        exact equivariant_of_spanVec _ _ equivariant_A hu
      · intro u hu
        rw [rep10_m12b, rB_eq]
        exact equivariant_of_spanVec _ _ equivariant_B hu
    · intro g h hg hh u hu
      have hu' : ∑ i, permAct (h : Equiv.Perm (Fin 12)) u i = 0 := by
        rw [sum_permAct]
        exact hu
      rw [Subgroup.coe_mul, permAct_mul, hg _ hu', hh _ hu, map_mul, Matrix.mulVec_mulVec]
  exact key g u hu

theorem m12M_ones : m12M *ᵥ (fun _ => (1 : ZMod 2)) = 0 := by decide +kernel

theorem m12M_mul_m12N : m12M * m12N = 1 := by decide +kernel

theorem vecMul_m12N : Matrix.vecMul (fun _ : Fin 12 => (1 : ZMod 2)) m12N = 0 := by
  decide +kernel

theorem m12_D : ∀ i, ∃ c : ZMod 2, (1 + m12N * m12M) *ᵥ spanVec i = c • (fun _ => (1 : ZMod 2)) := by
  decide +kernel

theorem m12M_surjective (x : Fin 10 → ZMod 2) :
    ∃ u : Fin 12 → ZMod 2, ∑ i, u i = 0 ∧ m12M *ᵥ u = x := by
  refine ⟨m12N *ᵥ x, ?_, ?_⟩
  · have h1 : (fun _ : Fin 12 => (1 : ZMod 2)) ⬝ᵥ (m12N *ᵥ x) = ∑ i, (m12N *ᵥ x) i := by
      simp [dotProduct]
    rw [← h1, Matrix.dotProduct_mulVec, vecMul_m12N]
    simp
  · rw [Matrix.mulVec_mulVec, m12M_mul_m12N, Matrix.one_mulVec]

theorem m12M_ker {u : Fin 12 → ZMod 2} (hu : ∑ i, u i = 0) (h : m12M *ᵥ u = 0) :
    u = 0 ∨ ∀ i, u i = 1 := by
  choose c hc using m12_D
  have h1 : (1 + m12N * m12M) *ᵥ u = u := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero,
      add_zero]
  have h2 : (1 + m12N * m12M) *ᵥ u = (∑ i, u i * c i) • (fun _ => (1 : ZMod 2)) := by
    conv_lhs => rw [eq_sum_spanVec hu]
    have := map_sum (Matrix.mulVecLin (1 + m12N * m12M)) (fun i => u i • spanVec i) Finset.univ
    simp only [Matrix.mulVecLin_apply] at this
    rw [this]
    funext j
    simp [Finset.sum_apply, Matrix.mulVec_smul, hc, Finset.sum_mul, mul_assoc]
  rw [h1] at h2
  have h3 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h3 (∑ i, u i * c i) with h4 | h4
  · left
    rw [h2, h4, zero_smul]
  · right
    intro i
    rw [h2, h4]
    simp

end Case0M12

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
