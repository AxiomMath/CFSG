module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardSigma

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

namespace SpinSigmaUVForms

open SpinWords

private def sigmaUVWord : List ℕ := [1, 2, 1, 2, 1, 2, 1, 0]

private def sigmaTUVWord : List ℕ := [1, 2, 1, 2, 1, 2, 1]

private theorem sigma_mul_uv_eq : s1A * s2A⁻¹ * (uA * vA) = wordElem sigmaUVWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordElem]
  show sigma1 * sigma2⁻¹ * (u * v) = wordPerm sigmaUVWord
  decide +kernel

private theorem sigma_mul_t_uv_eq : s1A * s2A⁻¹ * (tA * (uA * vA)) = wordElem sigmaTUVWord := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_wordElem]
  show sigma1 * sigma2⁻¹ * (x45 * (u * v)) = wordPerm sigmaTUVWord
  decide +kernel

private theorem q_eq_zero_of_fixed_sigmaUVWord :
    ∀ w : V, wordMat sigmaUVWord *ᵥ w = w → q w = 0 := by
  decide +kernel

private theorem exists_fixed_sigmaUVWord_not_fixed_Mx :
    ∃ w : V, wordMat sigmaUVWord *ᵥ w = w ∧ Mx *ᵥ w ≠ w := by
  decide +kernel

private theorem exists_fixed_sigmaTUVWord_q_eq_one :
    ∃ w : V, wordMat sigmaTUVWord *ᵥ w = w ∧ q w = 1 := by
  decide +kernel

private theorem card_fixed_sigmaUVWord_Mx :
    (Finset.univ.filter fun w : V => wordMat sigmaUVWord *ᵥ w = w ∧ Mx *ᵥ w = w).card = 2 := by
  decide +kernel

end SpinSigmaUVForms

theorem sigma_mul_uv_pow_three : (s1A * s2A⁻¹ * (uA * vA)) ^ 3 = uA * vA := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
  show (sigma1 * sigma2⁻¹ * (u * v)) ^ 3 = u * v
  decide +kernel

theorem sigma_mul_uv_pow_four : (s1A * s2A⁻¹ * (uA * vA)) ^ 4 = s1A * s2A⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
  show (sigma1 * sigma2⁻¹ * (u * v)) ^ 4 = sigma1 * sigma2⁻¹
  decide +kernel

theorem sigma_mul_t_uv_pow_three : (s1A * s2A⁻¹ * (tA * (uA * vA))) ^ 3 = tA * (uA * vA) := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
  show (sigma1 * sigma2⁻¹ * (x45 * (u * v))) ^ 3 = x45 * (u * v)
  decide +kernel

theorem sigma_mul_t_uv_pow_four : (s1A * s2A⁻¹ * (tA * (uA * vA))) ^ 4 = s1A * s2A⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
  show (sigma1 * sigma2⁻¹ * (x45 * (u * v))) ^ 4 = sigma1 * sigma2⁻¹
  decide +kernel

theorem tA_mul_uvA_comm : tA * (uA * vA) = uA * vA * tA := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  show x45 * (u * v) = u * v * x45
  decide +kernel

private theorem rhoA_pow_fixed {g : A45} {w : V}
    (hw : ((rhoA g : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) (n : ℕ) :
    ((rhoA (g ^ n) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hw, ih]

theorem spin_fixed_of_fixed_sigma_mul_uv {w : V}
    (hw : ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    ((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  refine ⟨?_, ?_⟩
  · rw [← sigma_mul_uv_pow_four]
    exact rhoA_pow_fixed hw 4
  · rw [← sigma_mul_uv_pow_three]
    exact rhoA_pow_fixed hw 3

theorem spin_fixed_of_fixed_sigma_mul_t_uv {w : V}
    (hw : ((rhoA (s1A * s2A⁻¹ * (tA * (uA * vA))) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    ((rhoA (s1A * s2A⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (tA * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  refine ⟨?_, ?_⟩
  · rw [← sigma_mul_t_uv_pow_four]
    exact rhoA_pow_fixed hw 4
  · rw [← sigma_mul_t_uv_pow_three]
    exact rhoA_pow_fixed hw 3

theorem spin_q_eq_zero_of_fixed_sigma_mul_uv (w : V)
    (hw : ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    q w = 0 := by
  rw [SpinSigmaUVForms.sigma_mul_uv_eq, SpinWords.rhoA_wordElem] at hw
  exact SpinSigmaUVForms.q_eq_zero_of_fixed_sigmaUVWord w hw

theorem spin_exists_fixed_sigma_mul_uv_not_fixed_t :
    ∃ w : V, ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w ≠ w := by
  have htx : tA = (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) := rfl
  rw [SpinSigmaUVForms.sigma_mul_uv_eq, SpinWords.rhoA_wordElem, htx, rhoA_x]
  exact SpinSigmaUVForms.exists_fixed_sigmaUVWord_not_fixed_Mx

theorem spin_card_fixed_sigma_mul_uv_t :
    (Finset.univ.filter fun w : V =>
      ((rhoA (s1A * s2A⁻¹ * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
        ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w).card = 2 := by
  have htx : tA = (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) := rfl
  rw [SpinSigmaUVForms.sigma_mul_uv_eq, SpinWords.rhoA_wordElem, htx, rhoA_x]
  exact SpinSigmaUVForms.card_fixed_sigmaUVWord_Mx

theorem spin_exists_fixed_sigma_mul_t_uv_q_eq_one :
    ∃ w : V,
      ((rhoA (s1A * s2A⁻¹ * (tA * (uA * vA))) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
        q w = 1 := by
  rw [SpinSigmaUVForms.sigma_mul_t_uv_eq, SpinWords.rhoA_wordElem]
  exact SpinSigmaUVForms.exists_fixed_sigmaTUVWord_q_eq_one

end CFSG.RankThree.GF2n.Parrott
