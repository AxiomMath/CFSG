module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

namespace Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.SteinbergBS

variable {K : Type} [Field K]

@[expose] def tMat (α β : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  !![(α : K), 0, 0, 0; 0, (β : K), 0, 0; 0, 0, ((β⁻¹ : Kˣ) : K), 0; 0, 0, 0, ((α⁻¹ : Kˣ) : K)]

theorem tMat_mul (α β α' β' : Kˣ) : tMat α β * tMat α' β' = tMat (α * α') (β * β') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem tMat_one : tMat (1 : Kˣ) (1 : Kˣ) = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat]

theorem tMat_mem (α β : Kˣ) : (tMat α β)ᵀ * minorJ K * tMat α β = minorJ K := by
  ext k j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases j <;> simp [tMat]

@[expose] def tElt (α β : Kˣ) : antiSp K :=
  ⟨⟨tMat α β, tMat α⁻¹ β⁻¹, by rw [tMat_mul, mul_inv_cancel, mul_inv_cancel, tMat_one],
    by rw [tMat_mul, inv_mul_cancel, inv_mul_cancel, tMat_one]⟩, tMat_mem α β⟩

theorem glMat_tElt (α β : Kˣ) : glMat (tElt α β : GL (Fin 4) K) = tMat α β := rfl

theorem tElt_mul (α β α' β' : Kˣ) : tElt α β * tElt α' β' = tElt (α * α') (β * β') :=
  antiSp_ext (by
    show tMat α β * tMat α' β' = tMat (α * α') (β * β')
    exact tMat_mul _ _ _ _)

theorem tElt_one : tElt (1 : Kˣ) (1 : Kˣ) = (1 : antiSp K) :=
  antiSp_ext tMat_one

theorem tElt_inv (α β : Kˣ) : (tElt α β)⁻¹ = (tElt α⁻¹ β⁻¹ : antiSp K) :=
  antiSp_ext rfl

theorem tElt_comm (α β α' β' : Kˣ) :
    tElt α β * tElt α' β' = (tElt α' β' * tElt α β : antiSp K) := by
  rw [tElt_mul, tElt_mul, mul_comm α, mul_comm β]

variable (K) in
@[expose] def tHom : Kˣ × Kˣ →* antiSp K where
  toFun p := tElt p.1 p.2
  map_one' := tElt_one
  map_mul' p q := (tElt_mul p.1 p.2 q.1 q.2).symm

theorem tHom_apply (α β : Kˣ) : tHom K (α, β) = tElt α β := rfl

theorem tElt_pow (α β : Kˣ) (j : ℕ) : (tElt α β : antiSp K) ^ j = tElt (α ^ j) (β ^ j) := by
  have := map_pow (tHom K) (α, β) j
  simpa [tHom_apply] using this.symm

variable [CharP K 2]

theorem tElt_conj_uElt (α β : Kˣ) (a b c d : K) :
    tElt α β * uElt a b c d * (tElt α β)⁻¹ =
      uElt ((α : K) * (β : K)⁻¹ * a) ((α : K) * β * b) ((α : K) ^ 2 * c) ((β : K) ^ 2 * d) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply antiSp_ext
  have hα : (α : K) ≠ 0 := α.ne_zero
  have hβ : (β : K) ≠ 0 := β.ne_zero
  show tMat α β * uMat a b c d = uMat _ _ _ _ * tMat α β
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, uMat, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem tElt_conj_mem {x : antiSp K} (hx : x ∈ antiUnipotent K) (α β : Kˣ) :
    tElt α β * x * (tElt α β)⁻¹ ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  rw [tElt_conj_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

omit [CharP K 2] in
@[expose] def Upper (g : antiSp K) : Prop :=
  ∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) K) i j = 0

omit [CharP K 2] in
theorem upper_tElt (α β : Kˣ) : Upper (tElt α β : antiSp K) := by
  intro i j hij
  rw [glMat_tElt]
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [tMat]

theorem exists_eq_mul_tElt {g : antiSp K} (hg : Upper g) :
    ∃ u ∈ antiUnipotent K, ∃ α β : Kˣ, g = u * tElt α β ∧ (α : K) = glMat (g : GL (Fin 4) K) 0 0 ∧
      (β : K) = glMat (g : GL (Fin 4) K) 1 1 := by
  obtain ⟨d0, d1, d2, d3⟩ := upper_diag_ne_zero hg
  obtain ⟨R1, R2, R3⟩ := upper_relations hg
  refine ⟨g * (tElt (Units.mk0 _ d0) (Units.mk0 _ d1))⁻¹, ?_, Units.mk0 _ d0, Units.mk0 _ d1,
    by group, rfl, rfl⟩
  rw [mem_antiUnipotent_iff_upper]
  set G := glMat (g : GL (Fin 4) K) with hG
  have hmul : glMat ((g * (tElt (Units.mk0 _ d0) (Units.mk0 _ d1))⁻¹ : antiSp K) : GL (Fin 4) K) =
      G * tMat (Units.mk0 _ d0)⁻¹ (Units.mk0 _ d1)⁻¹ := rfl
  rw [hmul]
  have h10 : G 1 0 = 0 := hg 1 0 (by decide)
  have h20 : G 2 0 = 0 := hg 2 0 (by decide)
  have h30 : G 3 0 = 0 := hg 3 0 (by decide)
  have h21 : G 2 1 = 0 := hg 2 1 (by decide)
  have h31 : G 3 1 = 0 := hg 3 1 (by decide)
  have h32 : G 3 2 = 0 := hg 3 2 (by decide)
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | simp [tMat, Matrix.mul_apply, Fin.sum_univ_four, h10,
        h20, h30, h21, h31, h32]
  · fin_cases i
    · simp [tMat, Matrix.mul_apply, Fin.sum_univ_four, d0]
    · simp [tMat, Matrix.mul_apply, Fin.sum_univ_four, d1]
    · simp [tMat, Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination R2
    · simp [tMat, Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination R1

theorem mul_tElt_conj_mem {u : antiSp K} (hu : u ∈ antiUnipotent K) (α β : Kˣ) {x : antiSp K}
    (hx : x ∈ antiUnipotent K) : (u * tElt α β) * x * (u * tElt α β)⁻¹ ∈ antiUnipotent K := by
  have h := mul_mem (mul_mem hu (tElt_conj_mem hx α β)) (inv_mem hu)
  convert h using 1
  group

theorem mem_normalizer_iff_upper {g : antiSp K} :
    g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ↔ Upper g := by
  constructor
  · exact upper_of_mem_normalizer
  · intro hg
    obtain ⟨u, hu, α, β, rfl, -, -⟩ := exists_eq_mul_tElt hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => mul_tElt_conj_mem hu α β hx
    · intro hx
      have h := mul_mem (mul_mem (inv_mem hu) hx) hu
      have h2 := tElt_conj_mem h α⁻¹ β⁻¹
      rw [← tElt_inv] at h2
      convert h2 using 1
      group

theorem quot_comm {a b : antiSp K}
    (ha : a ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)))
    (hb : b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) :
    a * b * a⁻¹ * b⁻¹ ∈ antiUnipotent K := by
  obtain ⟨u₁, hu₁, α₁, β₁, rfl, -, -⟩ := exists_eq_mul_tElt (mem_normalizer_iff_upper.mp ha)
  obtain ⟨u₂, hu₂, α₂, β₂, rfl, -, -⟩ := exists_eq_mul_tElt (mem_normalizer_iff_upper.mp hb)
  have hc : tElt α₂ β₂ * (tElt α₁ β₁)⁻¹ = (tElt α₁ β₁)⁻¹ * tElt α₂ β₂ := by
    rw [tElt_inv]
    exact (tElt_comm _ _ _ _).symm
  have v1 := tElt_conj_mem hu₂ α₁ β₁
  have v2 := tElt_conj_mem hu₁ α₂ β₂
  have key : (u₁ * tElt α₁ β₁) * (u₂ * tElt α₂ β₂) * (u₁ * tElt α₁ β₁)⁻¹ *
      (u₂ * tElt α₂ β₂)⁻¹ = (u₁ * (tElt α₁ β₁ * u₂ * (tElt α₁ β₁)⁻¹)) *
        (u₂ * (tElt α₂ β₂ * u₁ * (tElt α₂ β₂)⁻¹))⁻¹ := by
    calc (u₁ * tElt α₁ β₁) * (u₂ * tElt α₂ β₂) * (u₁ * tElt α₁ β₁)⁻¹ * (u₂ * tElt α₂ β₂)⁻¹
        = u₁ * tElt α₁ β₁ * u₂ * (tElt α₂ β₂ * (tElt α₁ β₁)⁻¹) * u₁⁻¹ * (tElt α₂ β₂)⁻¹ * u₂⁻¹ := by
          group
      _ = u₁ * tElt α₁ β₁ * u₂ * ((tElt α₁ β₁)⁻¹ * tElt α₂ β₂) * u₁⁻¹ * (tElt α₂ β₂)⁻¹ * u₂⁻¹ := by
          rw [hc]
      _ = _ := by group
  rw [key]
  exact mul_mem (mul_mem hu₁ v1) (inv_mem (mul_mem hu₂ v2))

end Sp4

end E68Proof

end E6

end CFSG.Quasithin
