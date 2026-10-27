module

public import CFSG.RankThree.GF2n.Smith81.S81BNAut
public import CFSG.RankThree.GF2n.Smith81.S81A5Beta

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

theorem beta_right_nondeg (η : Cube K) (h : ∀ ξ : Cube K, beta K ξ η = 0) : η = 0 := by
  have hc : ∀ I : Set.powersetCard (Fin 6) 3, coord K η I = 0 := by
    intro I
    have h1 := beta_cubeBasis_cmpl_apply η I
    rw [h (cubeBasis K (cmpl I))] at h1
    have h2 : beta K (cubeBasis K (cmpl I)) (cubeBasis K I) ≠ 0 :=
      beta_cubeBasis_ne_zero_of_disjoint (K := K) (disjoint_cmpl_left I)
    exact (mul_eq_zero.mp h1.symm).resolve_right h2
  refine (cubeBasis K).ext_elem fun I => ?_
  rw [map_zero, Finsupp.zero_apply]
  exact hc I

theorem bilinear_eq_smul_beta (B' : Cube K →ₗ[K] Cube K →ₗ[K] K)
    (hinv : ∀ g : GL (Fin 6) K,
      (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
        ∀ u v : Cube K, B' (rho K g u) (rho K g v) = B' u v) :
    ∃ lam : K, ∀ u v : Cube K, B' u v = lam * beta K u v := by
  haveI : FiniteDimensional K (Cube K) := Module.Finite.of_basis (cubeBasis K)
  have rho_one_QF1 : rho K (1 : GL (Fin 6) K) = 1 := map_one (TauCeti.extPowerRep K 6 3)
  have hinj : Function.Injective (beta K).flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine beta_right_nondeg w fun ξ => ?_
    have h1 := LinearMap.congr_fun hw ξ
    rw [LinearMap.flip_apply, LinearMap.zero_apply] at h1
    exact h1
  have hdim : Module.finrank K (Cube K) = Module.finrank K (Module.Dual K (Cube K)) :=
    Subspace.dual_finrank_eq.symm
  have hsurj : Function.Surjective (beta K).flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨eD, heD⟩ : ∃ eD : Cube K ≃ₗ[K] Cube K →ₗ[K] K, ∀ x, eD x = (beta K).flip x :=
    ⟨LinearEquiv.ofBijective (beta K).flip ⟨hinj, hsurj⟩, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Cube K →ₗ[K] Cube K, ∀ u w, beta K u (T w) = B' u w := by
    refine ⟨eD.symm.toLinearMap ∘ₗ B'.flip, fun u w => ?_⟩
    have h1 : (beta K).flip (eD.symm (B'.flip w)) = B'.flip w := by
      rw [← heD]
      exact eD.apply_symm_apply _
    have h2 := LinearMap.congr_fun h1 u
    simp only [LinearMap.flip_apply] at h2
    exact h2
  have hcomm : ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ∀ ξ, T (rho K g ξ) = rho K g (T ξ) := by
    intro g hg v
    have key : ∀ u, beta K u (T (rho K g v) - rho K g (T v)) = 0 := by
      intro u
      have hu : u = rho K g (rho K g⁻¹ u) := by
        rw [← Module.End.mul_apply, ← rho_mul, mul_inv_cancel, rho_one_QF1,
          Module.End.one_apply]
      obtain ⟨u', rfl⟩ : ∃ u', u = rho K g u' := ⟨_, hu⟩
      rw [map_sub, sub_eq_zero, hT, hinv g hg u' v, beta_rho, hg, one_mul, hT]
    exact sub_eq_zero.mp (beta_right_nondeg _ key)
  obtain ⟨c, hc⟩ := commutes_scalar T hcomm
  exact ⟨c, fun u v => by rw [← hT u v, hc v, map_smul, smul_eq_mul]⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
