module

public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL4Lin

open Matrix

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

@[expose] def conjEquiv (e : V ≃ₗ[K] W) : (V ≃ₗ[K] V) →* (W ≃ₗ[K] W) where
  toFun f := e.symm.trans (f.trans e)
  map_one' := by
    ext w
    simp
  map_mul' f g := by
    ext w
    simp

theorem conjEquiv_apply (e : V ≃ₗ[K] W) (f : V ≃ₗ[K] V) (w : W) :
    conjEquiv e f w = e (f (e.symm w)) := rfl

theorem conjEquiv_eq_one_iff (e : V ≃ₗ[K] W) (f : V ≃ₗ[K] V) : conjEquiv e f = 1 ↔ f = 1 := by
  constructor
  · intro h
    ext v
    have h1 := LinearEquiv.congr_fun h (e v)
    rw [conjEquiv_apply, LinearEquiv.symm_apply_apply] at h1
    exact e.injective h1
  · intro h
    rw [h, map_one]

variable {H : Type*} [Group H]

@[expose] noncomputable def matOf (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) (h : H) :
    Matrix (Fin 4) (Fin 4) K :=
  LinearMap.toMatrix' ((conjEquiv e (ψ h) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    (Fin 4 → K) →ₗ[K] (Fin 4 → K))

theorem matOf_mulVec (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) (h : H) (v : V) :
    matOf e ψ h *ᵥ e v = e (ψ h v) := by
  rw [matOf, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, conjEquiv_apply,
    LinearEquiv.symm_apply_apply]

theorem matOf_mul (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) (h k : H) :
    matOf e ψ (h * k) = matOf e ψ h * matOf e ψ k := by
  rw [matOf, matOf, matOf, ← LinearMap.toMatrix'_comp]
  congr 1
  ext w i
  simp [conjEquiv_apply]

theorem matOf_one (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) : matOf e ψ 1 = 1 := by
  rw [matOf, map_one, map_one]
  exact LinearMap.toMatrix'_id

theorem matOf_eq_one_iff (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) (h : H) :
    matOf e ψ h = 1 ↔ ψ h = 1 := by
  rw [← conjEquiv_eq_one_iff e (ψ h)]
  constructor
  · intro h1
    refine LinearEquiv.ext fun w => ?_
    have h2 := congrArg (fun A => A *ᵥ w) h1
    simp only [Matrix.one_mulVec] at h2
    rw [matOf, LinearMap.toMatrix'_mulVec] at h2
    exact h2
  · intro h1
    rw [matOf, h1]
    exact LinearMap.toMatrix'_id

theorem det_matOf (e : V ≃ₗ[K] (Fin 4 → K)) (ψ : H →* (V ≃ₗ[K] V)) (h : H) :
    (matOf e ψ h).det = (LinearEquiv.det (ψ h) : K) := by
  rw [matOf, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  show LinearMap.det ((e : V →ₗ[K] (Fin 4 → K)) ∘ₗ (ψ h : V →ₗ[K] V) ∘ₗ
    (e.symm : (Fin 4 → K) →ₗ[K] V)) = _
  exact LinearMap.det_conj _ e

theorem exists_sl4_of_linear [Finite K] (hV : Module.finrank K V = 4) (ψ : H →* (V ≃ₗ[K] V))
    (hperf : ∀ h : H, ψ h ∈ ⁅ψ.range, ψ.range⁆)
    (hcard : Nat.card ψ.range = Nat.card (Matrix.SpecialLinearGroup (Fin 4) K)) :
    ∃ (η : H →* Matrix.SpecialLinearGroup (Fin 4) K) (e : V ≃ₗ[K] (Fin 4 → K)),
      Function.Surjective η ∧ (∀ h : H, η h = 1 ↔ ψ h = 1) ∧
        ∀ (h : H) (v : V), e (ψ h v) = η h • e v := by
  classical
  have hfin : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  let e : V ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofFinrankEq V (Fin 4 → K) (by simp [hV])
  have hdet : ∀ h : H, (matOf e ψ h).det = 1 := by
    intro h
    rw [det_matOf]
    have hc : ψ h ∈ commutator (V ≃ₗ[K] V) :=
      (Subgroup.commutator_mono le_top le_top) (hperf h)
    have h1 := Abelianization.commutator_subset_ker (LinearEquiv.det (R := K) (M := V)) hc
    rw [MonoidHom.mem_ker] at h1
    rw [h1, Units.val_one]
  let η : H →* Matrix.SpecialLinearGroup (Fin 4) K :=
    { toFun := fun h => ⟨matOf e ψ h, hdet h⟩
      map_one' := Subtype.ext (matOf_one e ψ)
      map_mul' := fun h k => Subtype.ext (matOf_mul e ψ h k) }
  have hη : ∀ h : H, η h = 1 ↔ ψ h = 1 := by
    intro h
    rw [← matOf_eq_one_iff e ψ h]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  refine ⟨η, e, ?_, hη, fun h v => ?_⟩
  · have hker : η.ker = ψ.ker := by
      ext h
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact hη h
    have hc : Nat.card η.range = Nat.card ψ.range :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange η).toEquiv).symm.trans
        ((Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv).trans
          (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv))
    have htop : η.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hc.trans hcard)
    exact MonoidHom.range_eq_top.mp htop
  · rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact (matOf_mulVec e ψ h v).symm

end CFSG.RankThree.GF2n.Stroth80.SL4Lin
