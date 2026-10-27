module

public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitaryTwo
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary

public section

open scoped commutatorElement

namespace CFSG.Quasithin

open CFSG.Open Matrix

section Matrices

variable {F : Type} [Field F]

@[expose] def suTwoD (g : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, g, 0; 0, 0, g ^ 2]

@[expose] def suTwoDinv (g : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, g ^ 2, 0; 0, 0, g]

@[expose] def suTwoP : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def suTwoPinv : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem suTwoD_mul_inv {g : F} (h : g ^ 3 = 1) : suTwoD g * suTwoDinv g = 1 := by
  have h1 : g * g ^ 2 = 1 := by rw [← pow_succ']; exact h
  have h2 : g ^ 2 * g = 1 := by rw [← pow_succ]; exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoD, suTwoDinv, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

theorem suTwoDinv_mul {g : F} (h : g ^ 3 = 1) : suTwoDinv g * suTwoD g = 1 := by
  have h1 : g * g ^ 2 = 1 := by rw [← pow_succ']; exact h
  have h2 : g ^ 2 * g = 1 := by rw [← pow_succ]; exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoD, suTwoDinv, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

theorem suTwoP_mul_inv : (suTwoP : Matrix (Fin 3) (Fin 3) F) * suTwoPinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoP, suTwoPinv, Matrix.mul_apply, Fin.sum_univ_three]

theorem suTwoPinv_mul : (suTwoPinv : Matrix (Fin 3) (Fin 3) F) * suTwoP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoP, suTwoPinv, Matrix.mul_apply, Fin.sum_univ_three]

theorem suTwo_comm (g : F) :
    (suTwoP : Matrix (Fin 3) (Fin 3) F) * suTwoD g * suTwoPinv * suTwoDinv g =
      Matrix.scalar (Fin 3) (g ^ 2) := by
  have h3 : g * g = g ^ 2 := (sq g).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoP, suTwoPinv, suTwoD, suTwoDinv, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.scalar_apply, h3]

theorem det_suTwoD {g : F} (h : g ^ 3 = 1) : (suTwoD g).det = 1 := by
  have : g * g ^ 2 = 1 := by rw [← pow_succ']; exact h
  simp [suTwoD, Matrix.det_fin_three, this]

theorem det_suTwoP : (suTwoP : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [suTwoP, Matrix.det_fin_three]

theorem unitary_suTwoD {g : F} (h : g ^ 3 = 1) :
    ((suTwoD g).map (· ^ (2 ^ 1)))ᵀ * suTwoD g = 1 := by
  have h1 : (g ^ 2) ^ 2 * g ^ 2 = 1 := by
    rw [← pow_mul, ← pow_add, show 2 * 2 + 2 = 3 * 2 from rfl, pow_mul, h, one_pow]
  have h2 : g ^ 2 * g = 1 := by rw [← pow_succ]; exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, h2, h1]

theorem unitary_suTwoP : ((suTwoP : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ 1)))ᵀ * suTwoP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoP, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

end Matrices

section Main

variable {F : Type} [Field F] [Finite F]

@[expose] def suTwoDGL {g : F} (h : g ^ 3 = 1) : GL (Fin 3) F :=
  ⟨suTwoD g, suTwoDinv g, suTwoD_mul_inv h, suTwoDinv_mul h⟩

@[expose] def suTwoPGL : GL (Fin 3) F := ⟨suTwoP, suTwoPinv, suTwoP_mul_inv, suTwoPinv_mul⟩

omit [Finite F] in
theorem suTwoDGL_mem {g : F} (h : g ^ 3 = 1) : suTwoDGL h ∈ StatedSU 3 (2 ^ 1) F :=
  Subgroup.subset_closure ⟨det_suTwoD h, unitary_suTwoD h⟩

omit [Finite F] in
theorem suTwoPGL_mem : (suTwoPGL : GL (Fin 3) F) ∈ StatedSU 3 (2 ^ 1) F :=
  Subgroup.subset_closure ⟨det_suTwoP, unitary_suTwoP⟩

theorem statedSU_one_kernel_le_commutator (hF : Nat.card F = (2 ^ 1) ^ 2) :
    (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ 1) F) ≤
      commutator (StatedSU 3 (2 ^ 1) F) := by
  have hU : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, hF]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hg3 : g ^ 3 = 1 := by
    rw [← hU]
    exact pow_card_eq_one'
  have hζ : (g : F) ^ 3 = 1 := by
    have := congrArg Units.val hg3
    simpa using this
  set P : StatedSU 3 (2 ^ 1) F := ⟨suTwoPGL, suTwoPGL_mem⟩ with hP
  set D : StatedSU 3 (2 ^ 1) F := ⟨suTwoDGL hζ, suTwoDGL_mem hζ⟩ with hD
  have hc0 : ((⁅P, D⁆ : StatedSU 3 (2 ^ 1) F) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (g ^ 2) := by
    refine Units.ext ?_
    have h1 : (((⁅P, D⁆ : StatedSU 3 (2 ^ 1) F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        suTwoP * suTwoD (g : F) * suTwoPinv * suTwoDinv (g : F) := rfl
    rw [h1, suTwo_comm]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_pow]
  have hmem : (⁅P, D⁆ : StatedSU 3 (2 ^ 1) F) ∈ commutator (StatedSU 3 (2 ^ 1) F) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  intro z hz
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg c))
  have hkey : (g ^ 2) ^ (2 * k) = g ^ k := by
    rw [← pow_mul, show 2 * (2 * k) = 3 * k + k by ring, pow_add, pow_mul, hg3, one_pow,
      one_mul]
  have hz' : z = ⁅P, D⁆ ^ (2 * k) := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, hc0, ← map_pow, hkey, hk]
    exact hc.symm
  rw [hz']
  exact Subgroup.pow_mem _ hmem _

theorem isRankOneSylow_statedSU_one (hF : Nat.card F = (2 ^ 1) ^ 2) :
    IsRankOneSylow (StatedSU 3 (2 ^ 1) F) := by
  refine isRankOneSylow_of_central_cover
    (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ 1) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ ?_ (isRankOneSylowCyclic_statedProj_one hF)
  · rw [QuotientGroup.ker_mk']
    exact statedSU_scalars_le_center
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    exact statedSU_three_scalars_odd z hz
  · rw [QuotientGroup.ker_mk']
    exact statedSU_one_kernel_le_commutator hF

end Main

end CFSG.Quasithin
