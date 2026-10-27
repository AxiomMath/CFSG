module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.SteinbergCBTwistedIsometry

public section

namespace CFSG.Quasithin.G11.Harris.L2

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.SteinbergCB
open scoped MatrixGroups

section Conj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {U : Type} [AddCommGroup U] [Module K U]

@[expose] noncomputable def conjGL (τ : U ≃ₗ[K] (ι → K)) : (U ≃ₗ[K] U) ≃* GL ι K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv τ).trans Matrix.GeneralLinearGroup.toLin.symm)

theorem conjGL_mulVec (τ : U ≃ₗ[K] (ι → K)) (g : U ≃ₗ[K] U) (v : ι → K) :
    (conjGL τ g : Matrix ι ι K) *ᵥ v = τ (g (τ.symm v)) := by
  have h : Matrix.GeneralLinearGroup.toLin (conjGL τ g) =
      (LinearMap.GeneralLinearGroup.congrLinearEquiv τ)
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm g) := by
    simp [conjGL]
  have := congrArg (fun x : LinearMap.GeneralLinearGroup K (ι → K) => (x : (ι → K) →ₗ[K] ι → K) v) h
  simp at this
  exact this

theorem conjGL_preserves_iff (τ : U ≃ₗ[K] (ι → K)) (Q : QuadraticForm K U) (Q' : (ι → K) → K)
    (hQ : ∀ u, Q' (τ u) = Q u) (g : U ≃ₗ[K] U) :
    (∀ v, Q' ((conjGL τ g : Matrix ι ι K) *ᵥ v) = Q' v) ↔ g ∈ isometryGroup Q := by
  rw [mem_isometryGroup]
  constructor
  · intro h x
    have := h (τ x)
    rwa [conjGL_mulVec, LinearEquiv.symm_apply_apply, hQ, hQ] at this
  · intro h v
    rw [conjGL_mulVec, hQ, h, ← hQ, LinearEquiv.apply_symm_apply]

theorem statedOmega_eq_map (τ : U ≃ₗ[K] (ι → K)) (Q : QuadraticForm K U) (Q' : (ι → K) → K)
    (hQ : ∀ u, Q' (τ u) = Q u) :
    StatedOmega Q' = ⁅isometryGroup Q, isometryGroup Q⁆.map (conjGL τ).toMonoidHom := by
  have hset : {A : GL ι K | ∀ v, Q' ((A : Matrix ι ι K) *ᵥ v) = Q' v} =
      ((isometryGroup Q).map (conjGL τ).toMonoidHom : Set (GL ι K)) := by
    ext A
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨(conjGL τ).symm A, ?_, by simp⟩
      rw [← conjGL_preserves_iff τ Q Q' hQ]
      simpa using h
    · rintro ⟨g, hg, rfl⟩
      exact (conjGL_preserves_iff τ Q Q' hQ g).2 hg
  rw [StatedOmega, hset, Subgroup.closure_eq, Subgroup.map_commutator]

end Conj

section Map

variable {K K' : Type} [Field K] [Field K'] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_mulVec_comp (e : K ≃+* K') (A : GL ι K) (v : ι → K) :
    (Matrix.GeneralLinearGroup.map (e : K →+* K') A : Matrix ι ι K') *ᵥ (fun i => e (v i)) =
      fun i => e (((A : Matrix ι ι K) *ᵥ v) i) := by
  funext i
  have := RingHom.map_mulVec (e : K →+* K') (A : Matrix ι ι K) v i
  exact this.symm

theorem preserves_map_iff (e : K ≃+* K') (Q : (ι → K) → K) (Q' : (ι → K') → K')
    (hQ : ∀ v, Q' (fun i => e (v i)) = e (Q v)) (A : GL ι K) :
    (∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v) ↔
      ∀ v', Q' ((Matrix.GeneralLinearGroup.map (e : K →+* K') A : Matrix ι ι K') *ᵥ v') = Q' v' := by
  constructor
  · intro h v'
    have hv : v' = fun i => e (e.symm (v' i)) := by funext i; simp
    rw [hv, map_mulVec_comp, hQ, hQ, h]
  · intro h v
    apply e.injective
    rw [← hQ, ← hQ, ← map_mulVec_comp, h]

theorem statedOmega_map_eq (e : K ≃+* K') (Q : (ι → K) → K) (Q' : (ι → K') → K')
    (hQ : ∀ v, Q' (fun i => e (v i)) = e (Q v)) :
    StatedOmega Q' = (StatedOmega Q).map (Matrix.GeneralLinearGroup.map (e : K →+* K')) := by
  have hset : {A' : GL ι K' | ∀ v, Q' ((A' : Matrix ι ι K') *ᵥ v) = Q' v} =
      (Matrix.GeneralLinearGroup.map (e : K →+* K')) ''
        {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} := by
    ext A'
    constructor
    · intro h
      refine ⟨Matrix.GeneralLinearGroup.map (e.symm : K' →+* K) A', ?_, ?_⟩
      · rw [Set.mem_ofPred_eq, preserves_map_iff e Q Q' hQ]
        have : Matrix.GeneralLinearGroup.map (e : K →+* K')
            (Matrix.GeneralLinearGroup.map (e.symm : K' →+* K) A') = A' := by
          ext i j; simp
        rw [this]
        exact h
      · ext i j; simp
    · rintro ⟨A, hA, rfl⟩
      exact (preserves_map_iff e Q Q' hQ A).1 hA
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, MonoidHom.map_closure, hset]

end Map

end CFSG.Quasithin.G11.Harris.L2
