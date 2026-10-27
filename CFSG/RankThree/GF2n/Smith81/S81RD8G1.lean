module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81RDot

open Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

private theorem pow_four_core [CharP K 2] (P : Matrix (Fin 6) (Fin 6) K)
    {a b f g : Fin 6 → K}
    (hfa : f ⬝ᵥ a = 0) (hgb : g ⬝ᵥ b = 0)
    (hF : ∀ z : Fin 6 → K, f ⬝ᵥ (P *ᵥ z) = f ⬝ᵥ z + (f ⬝ᵥ b) * (g ⬝ᵥ z))
    (hG : ∀ z : Fin 6 → K,
      g ⬝ᵥ (P *ᵥ z) = (g ⬝ᵥ a) * (f ⬝ᵥ z) + (1 + (f ⬝ᵥ b) * (g ⬝ᵥ a)) * (g ⬝ᵥ z))
    (l : K) (hl : (P ^ 4) *ᵥ a = l • a) :
    (f ⬝ᵥ b) * (g ⬝ᵥ a) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hPpow : ∀ v : Fin 6 → K, (P ^ 4) *ᵥ v = P *ᵥ (P *ᵥ (P *ᵥ (P *ᵥ v))) := by
    intro v
    simp only [pow_succ, pow_zero, one_mul, ← Matrix.mulVec_mulVec]
  have hchain : P *ᵥ (P *ᵥ (P *ᵥ (P *ᵥ a))) = l • a := by
    rw [← hPpow a, hl]
  have hfin : f ⬝ᵥ (P *ᵥ (P *ᵥ (P *ᵥ (P *ᵥ a)))) = 0 := by
    rw [hchain, dotProduct_smul, hfa, smul_zero]
  simp only [hF, hG, hfa] at hfin
  have hpoly : ((f ⬝ᵥ b) * (g ⬝ᵥ a)) ^ 4 = 0 := by
    linear_combination hfin - (3 * ((f ⬝ᵥ b) * (g ⬝ᵥ a)) ^ 3 + 5 * ((f ⬝ᵥ b) * (g ⬝ᵥ a)) ^ 2
      + 2 * ((f ⬝ᵥ b) * (g ⬝ᵥ a))) * h2
  exact (pow_eq_zero_iff (by norm_num)).mp hpoly

theorem transvec_cases_of_rho_pow_four [CharP K 2] {x y : GL (Fin 6) K} {a f b g : Fin 6 → K}
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hy : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec b g)
    (hfa : f ⬝ᵥ a = 0) (hgb : g ⬝ᵥ b = 0)
    (h : rho K ((x * y) ^ 4) = 1) : f ⬝ᵥ b = 0 ∨ g ⬝ᵥ a = 0 := by
  by_contra hne
  obtain ⟨hα, hβ⟩ := not_or.mp hne
  have hXv : ∀ v : Fin 6 → K, (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v = v + (f ⬝ᵥ v) • a := by
    intro v
    rw [hx, one_add_vecMulVec_mulVec]
  have hYv : ∀ v : Fin 6 → K, (y : Matrix (Fin 6) (Fin 6) K) *ᵥ v = v + (g ⬝ᵥ v) • b := by
    intro v
    rw [hy, one_add_vecMulVec_mulVec]
  have hPz : ∀ z : Fin 6 → K,
      ((x : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K)) *ᵥ z
        = z + (f ⬝ᵥ z + (g ⬝ᵥ z) * (f ⬝ᵥ b)) • a + (g ⬝ᵥ z) • b := by
    intro z
    rw [← Matrix.mulVec_mulVec, hYv z, Matrix.mulVec_add, Matrix.mulVec_smul, hXv z, hXv b]
    module
  have hF : ∀ z : Fin 6 → K,
      f ⬝ᵥ (((x : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K)) *ᵥ z)
        = f ⬝ᵥ z + (f ⬝ᵥ b) * (g ⬝ᵥ z) := by
    intro z
    rw [hPz z]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hfa, mul_zero, add_zero]
    ring
  have hG : ∀ z : Fin 6 → K,
      g ⬝ᵥ (((x : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K)) *ᵥ z)
        = (g ⬝ᵥ a) * (f ⬝ᵥ z) + (1 + (f ⬝ᵥ b) * (g ⬝ᵥ a)) * (g ⬝ᵥ z) := by
    intro z
    rw [hPz z]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hgb, mul_zero, add_zero]
    ring
  obtain ⟨l, -, hl⟩ := (rho_eq_one_iff _).mp h
  rw [Units.val_pow_eq_pow_val, Units.val_mul] at hl
  have hl' : ((x : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K)) ^ 4 *ᵥ a
      = l • a := by
    rw [hl, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact mul_ne_zero hα hβ (pow_four_core _ hfa hgb hF hG l hl')

end CFSG.RankThree.GF2n.Smith81.A5Cube
