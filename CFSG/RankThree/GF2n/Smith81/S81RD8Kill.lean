module

public import CFSG.RankThree.GF2n.Smith81.S81A5Root
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho

open Matrix exteriorPower

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

theorem rho_sub_one_add_centre {σ x t : GL (Fin 6) K} {a f θ : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a θ)
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (ht : (t : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a (θ + f)) :
    rho K t - 1 = (rho K σ - 1) + (rho K x - 1) := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) ?_
  rintro _ ⟨v, rfl⟩
  have hv : ιMulti K 3 v = ιMulti K 3 ![v 0, v 1, v 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [rho_sub_one_ιMulti ht (v 0) (v 1) (v 2), rho_sub_one_ιMulti hσ (v 0) (v 1) (v 2),
    rho_sub_one_ιMulti hx (v 0) (v 1) (v 2)]
  simp only [add_dotProduct, add_smul]
  module

theorem rho_sub_one_add_axis {σ x t : GL (Fin 6) K} {a w f : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w f)
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (ht : (t : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec (w + a) f) :
    rho K t - 1 = (rho K σ - 1) + (rho K x - 1) := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) ?_
  rintro _ ⟨v, rfl⟩
  have hv : ιMulti K 3 v = ιMulti K 3 ![v 0, v 1, v 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [rho_sub_one_ιMulti ht (v 0) (v 1) (v 2), rho_sub_one_ιMulti hσ (v 0) (v 1) (v 2),
    rho_sub_one_ιMulti hx (v 0) (v 1) (v 2)]
  simp only [ι3_add_fst, ι3_add_snd, ι3_add_thd, smul_add]
  module

private theorem sub_one_mul_sub_one_gen {M : Type} [AddCommGroup M] [Module K M]
    (f g : Module.End K M) :
    (f - 1) * (g - 1) = f * g - 1 - (f - 1) - (g - 1) := by
  noncomm_ring

theorem rho_kill_centre {σ x : GL (Fin 6) K} {a f θ : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a θ)
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) (hθa : θ ⬝ᵥ a = 0) :
    (rho K σ - 1) ∘ₗ (rho K x - 1) = 0 := by
  have hprod := one_add_mul_one_add_sub_one a a θ f
  rw [hθa, zero_smul, add_zero, ← Matrix.vecMulVec_add] at hprod
  have ht : ((σ * x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a (θ + f) := by
    rw [Units.val_mul, hσ, hx, ← hprod]
    abel
  have hkey := rho_sub_one_add_centre hσ hx ht
  rw [rho_mul] at hkey
  rw [← Module.End.mul_eq_comp, sub_one_mul_sub_one_gen (rho K σ) (rho K x), hkey]
  abel

theorem rho_kill_axis {σ x : GL (Fin 6) K} {a w f : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w f)
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) (hfa : f ⬝ᵥ a = 0) :
    (rho K σ - 1) ∘ₗ (rho K x - 1) = 0 := by
  have hprod := one_add_mul_one_add_sub_one w a f f
  rw [hfa, zero_smul, add_zero, ← Matrix.add_vecMulVec] at hprod
  have ht : ((σ * x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec (w + a) f := by
    rw [Units.val_mul, hσ, hx, ← hprod]
    abel
  have hkey := rho_sub_one_add_axis hσ hx ht
  rw [rho_mul] at hkey
  rw [← Module.End.mul_eq_comp, sub_one_mul_sub_one_gen (rho K σ) (rho K x), hkey]
  abel

end CFSG.RankThree.GF2n.Smith81.A5Cube
