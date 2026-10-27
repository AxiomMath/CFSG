module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Plane

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

structure Frame (σ : K ≃+* K) (n : ℕ) where
  e : Fin n → K
  u : Fin n → K
  z : Fin n → K
  he : herm σ e e = 0
  hu : herm σ u u = 0
  hz : herm σ z z = 0
  heu : herm σ e u = 1
  hez : herm σ e z = 0
  huz : herm σ u z = 0

namespace Frame

variable (P : Frame σ n)

theorem hue (hσ : ∀ c, σ (σ c) = c) : herm σ P.u P.e = 1 := by
  rw [herm_conj σ hσ, P.heu, map_one]

theorem hze (hσ : ∀ c, σ (σ c) = c) : herm σ P.z P.e = 0 :=
  herm_eq_zero_comm σ hσ P.hez

theorem hzu (hσ : ∀ c, σ (σ c) = c) : herm σ P.z P.u = 0 :=
  herm_eq_zero_comm σ hσ P.huz

end Frame

@[expose] def Aff (P : Frame σ n) (g : SUid σ n) (m : SpecialLinearGroup (Fin 2) (fixSub σ))
    (τ₁ τ₂ : K) : Prop :=
  g • P.z = P.z ∧ g • P.e = ent m 0 0 • P.e + ent m 1 0 • P.u + τ₁ • P.z ∧
    g • P.u = ent m 0 1 • P.e + ent m 1 1 • P.u + τ₂ • P.z

@[expose] def Triv (P : Frame σ n) (g : SUid σ n) : Prop :=
  ∀ y : Fin n → K, herm σ P.e y = 0 → herm σ P.u y = 0 → herm σ P.z y = 0 → g • y = y

theorem Aff.one (P : Frame σ n) : Aff P (1 : SUid σ n) 1 0 0 := by
  refine ⟨one_smul _ _, ?_, ?_⟩ <;> simp

theorem Triv.one (P : Frame σ n) : Triv P (1 : SUid σ n) := fun _ _ _ _ => one_smul _ _

theorem Triv.mul {P : Frame σ n} {g g' : SUid σ n} (h : Triv P g) (h' : Triv P g') :
    Triv P (g * g') := fun y h1 h2 h3 => by rw [mul_smul, h' y h1 h2 h3, h y h1 h2 h3]

theorem Triv.inv {P : Frame σ n} {g : SUid σ n} (h : Triv P g) : Triv P g⁻¹ :=
  fun y h1 h2 h3 => by rw [inv_smul_eq_iff]; exact (h y h1 h2 h3).symm

theorem Aff.mul {P : Frame σ n} {g g' : SUid σ n} {m m' : SpecialLinearGroup (Fin 2) (fixSub σ)}
    {τ₁ τ₂ τ₁' τ₂' : K} (h : Aff P g m τ₁ τ₂) (h' : Aff P g' m' τ₁' τ₂') :
    Aff P (g * g') (m * m') (ent m' 0 0 * τ₁ + ent m' 1 0 * τ₂ + τ₁')
      (ent m' 0 1 * τ₁ + ent m' 1 1 * τ₂ + τ₂') := by
  obtain ⟨hz, he, hu⟩ := h
  obtain ⟨hz', he', hu'⟩ := h'
  refine ⟨by rw [mul_smul, hz', hz], ?_, ?_⟩
  · rw [mul_smul, he', smul_add, smul_add, smul_comm g, smul_comm g, smul_comm g, he, hu, hz,
      ent_mul_zero_zero, ent_mul_one_zero]
    module
  · rw [mul_smul, hu', smul_add, smul_add, smul_comm g, smul_comm g, smul_comm g, he, hu, hz,
      ent_mul_zero_one, ent_mul_one_one]
    module

theorem ent_inv_zero_zero (g : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent g⁻¹ 0 0 = ent g 1 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem ent_inv_zero_one (g : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent g⁻¹ 0 1 = -ent g 0 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem ent_inv_one_zero (g : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent g⁻¹ 1 0 = -ent g 1 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem ent_inv_one_one (g : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent g⁻¹ 1 1 = ent g 0 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem Aff.inv {P : Frame σ n} {g : SUid σ n} {m : SpecialLinearGroup (Fin 2) (fixSub σ)}
    {τ₁ τ₂ : K} (h : Aff P g m τ₁ τ₂) :
    Aff P g⁻¹ m⁻¹ (-(ent m 1 1 * τ₁ - ent m 1 0 * τ₂)) (-(-ent m 0 1 * τ₁ + ent m 0 0 * τ₂)) := by
  obtain ⟨hz, he, hu⟩ := h
  have hdet := det_ent m
  refine ⟨?_, ?_, ?_⟩
  · rw [inv_smul_eq_iff]
    exact hz.symm
  · rw [ent_inv_zero_zero, ent_inv_one_zero, inv_smul_eq_iff, smul_add, smul_add, smul_comm g,
      smul_comm g, smul_comm g, he, hu, hz]
    match_scalars <;> first | ring1 | linear_combination (-1 : K) * hdet
  · rw [ent_inv_zero_one, ent_inv_one_one, inv_smul_eq_iff, smul_add, smul_add, smul_comm g,
      smul_comm g, smul_comm g, he, hu, hz]
    match_scalars <;> first | ring1 | linear_combination (-1 : K) * hdet

end CFSG.RankThree.PartOne.SEITZ5
