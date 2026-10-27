module

public import CFSG.RankThree.GF2n.Smith81.S81RFrame
public import CFSG.RankThree.GF2n.Smith81.S81NModel1

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private theorem ker_rho_conj [CharP K 2] (c g : GL (Fin 6) K) (ξ : Cube K) :
    rho K (c * g * c⁻¹) (rho K c ξ) = rho K c (rho K g ξ) := by
  have h1 : rho K (c * g * c⁻¹) * rho K c = rho K c * rho K g := by
    rw [← rho_mul, ← rho_mul, mul_assoc, inv_mul_cancel, mul_one]
  exact congrArg (fun f : Cube K →ₗ[K] Cube K => f ξ) h1

private theorem rho_apply_inv [CharP K 2] (c : GL (Fin 6) K) (ξ : Cube K) :
    rho K c⁻¹ (rho K c ξ) = ξ := by
  have h1 : rho K c⁻¹ * rho K c = 1 := by
    rw [← rho_mul, inv_mul_cancel]
    exact map_one (TauCeti.extPowerRep K 6 3)
  exact congrArg (fun f : Cube K →ₗ[K] Cube K => f ξ) h1

theorem ker_le_span_pure_of_isTransvec [Finite K] [CharP K 2] {g : GL (Fin 6) K}
    (hg : IsTransvec K g) :
    LinearMap.ker (rho K g - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K g - 1) ∧ IsPure K ξ} := by
  obtain ⟨c, hcdet, hcg⟩ := exists_conj_tInv1 hg
  have hker : ∀ ξ, ξ ∈ LinearMap.ker (rho K g - 1) ↔
      rho K c ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1) := by
    intro ξ
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [← hcg, ker_rho_conj]
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg (rho K c⁻¹) h
      rwa [rho_apply_inv, rho_apply_inv] at this
  intro ξ hξ
  have h1 : rho K c ξ ∈ Submodule.span K {η | η ∈ LinearMap.ker (rho K (tInv1 K) - 1) ∧
      IsPure K η} := model1_P1 ((hker ξ).mp hξ)
  have h2 := Submodule.mem_map_of_mem (f := (rho K c⁻¹ : Cube K →ₗ[K] Cube K)) h1
  rw [Submodule.map_span] at h2
  have h3 : ξ ∈ Submodule.span K ((rho K c⁻¹ : Cube K →ₗ[K] Cube K) ''
      {η | η ∈ LinearMap.ker (rho K (tInv1 K) - 1) ∧ IsPure K η}) := by
    simpa only [rho_apply_inv] using h2
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨η, ⟨hηC, hηP⟩, rfl⟩
  refine ⟨?_, hηP.rho c⁻¹⟩
  rw [hker]
  have : rho K c (rho K c⁻¹ η) = η := by
    have h1 : rho K c * rho K c⁻¹ = 1 := by
      rw [← rho_mul, mul_inv_cancel]
      exact map_one (TauCeti.extPowerRep K 6 3)
    exact congrArg (fun f : Cube K →ₗ[K] Cube K => f η) h1
  rw [this]
  exact hηC

end CFSG.RankThree.GF2n.Smith81.A5Cube
