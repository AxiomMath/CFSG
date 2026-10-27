module

public import CFSG.Quasithin.Vol2.Ch3E213MP5C
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.E2.TI2b.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.Ch3E213M.P5
open CFSG.Open CFSG.QuasithinUnique B6
open scoped MatrixGroups

variable {k : Type} [Field k]

theorem mem_stabilizer_of_mulVec_mem {g : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : (g : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k) ∈ flagSpace 3 k 1) :
    g ∈ stabilizer (flagSpace 3 k 1) := by
  rw [mem_stabilizer]
  have hgi : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
      (Pi.single 0 1 : Fin 3 → k) ∈ flagSpace 3 k 1 := by
    set l := ((g : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k)) 0 with hl
    have hg0 : (g : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k) =
        l • (Pi.single 0 1 : Fin 3 → k) := eq_smul_single_of_mem h
    have h1 : (Pi.single 0 1 : Fin 3 → k) = l •
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
          (Pi.single 0 1 : Fin 3 → k)) := by
      calc (Pi.single 0 1 : Fin 3 → k)
          = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k)) := by
            rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
        _ = _ := by rw [hg0, Matrix.mulVec_smul]
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at e0 e1 e2
    have hl0 : l ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e0
      simp at e0
    rw [mem_flagSpace_one]
    constructor
    · have : l * (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
          (Pi.single 0 1 : Fin 3 → k)) 1 = 0 := by simpa using e1.symm
      exact (mul_eq_zero.mp this).resolve_left hl0
    · have : l * (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
          (Pi.single 0 1 : Fin 3 → k)) 2 = 0 := by simpa using e2.symm
      exact (mul_eq_zero.mp this).resolve_left hl0
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [eq_smul_single_of_mem hv]
    simp only [mulVecLin_apply, Matrix.mulVec_smul]
    exact (flagSpace 3 k 1).smul_mem _ h
  · intro v hv
    refine ⟨((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v, ?_, ?_⟩
    · rw [eq_smul_single_of_mem hv, Matrix.mulVec_smul]
      exact (flagSpace 3 k 1).smul_mem _ hgi
    · simp only [mulVecLin_apply, Matrix.mulVec_mulVec, coe_mul_coe_inv, Matrix.one_mulVec]

theorem mem_normalizer_pa1_of_conj_pzz_le [Finite k] [CharP k 2]
    (hk : ∃ m : ℕ, Nat.card k = 2 ^ m) {x : projectiveSL 3 k} (hx : conjSub x (pzz k) ≤ pa1 k) :
    x ∈ Subgroup.normalizer (pa1 k : Set (projectiveSL 3 k)) := by
  obtain ⟨xt, rfl⟩ := proj_surjective 3 k x
  rw [normalizer_pa1_eq hk]
  have hz : proj 3 k (xt * uu 0 0 1 * xt⁻¹) ∈ pa1 k := by
    have h1 : proj 3 k (xt * uu 0 0 1 * xt⁻¹) ∈ conjSub (proj 3 k xt) (pzz k) := by
      rw [mem_conjSub, map_mul, map_mul, map_inv]
      have : (proj 3 k xt)⁻¹ * (proj 3 k xt * proj 3 k (uu 0 0 1) * (proj 3 k xt)⁻¹) *
          proj 3 k xt = proj 3 k (uu 0 0 1) := by group
      rw [this]
      exact ⟨uu 0 0 1, ⟨1, rfl⟩, rfl⟩
    exact hx h1
  obtain ⟨m, hm, hmπ⟩ := hz
  obtain ⟨c, hc3, hcm⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hmπ)
  obtain ⟨a, c', rfl⟩ := hm
  set M := xt * uu 0 0 1 * xt⁻¹ with hM
  have hMm : (M : Matrix (Fin 3) (Fin 3) k) =
      ((uu a 0 c' : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        scalar (Fin 3) (c : k) := by
    rw [← hcm, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hcoe : (M : Matrix (Fin 3) (Fin 3) k) = (xt : Matrix (Fin 3) (Fin 3) k) *
      ((uu (0 : k) 0 1 : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((xt⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    rw [hM]; simp
  have htrM : Matrix.trace (M : Matrix (Fin 3) (Fin 3) k) = 3 := by
    rw [hcoe, Matrix.trace_mul_cycle, coe_inv_mul_coe, Matrix.one_mul]
    simp [Matrix.trace, Fin.sum_univ_three, coe_uu]
    norm_num
  have htr2 : Matrix.trace (M : Matrix (Fin 3) (Fin 3) k) = 3 * (c : k) := by
    rw [hMm]
    simp [Matrix.trace, Fin.sum_univ_three, coe_uu, Matrix.mul_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    ring
  have h3 : (3 : k) = 1 := by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  have hc1 : (c : k) = 1 := by
    rw [htrM, h3, one_mul] at htr2
    exact htr2.symm
  have hMua : M ∈ ua1 k := by
    have : M = uu a 0 c' := by
      apply Subtype.ext
      rw [hMm, hc1]
      simp
    rw [this]
    exact ⟨a, c', rfl⟩
  obtain ⟨-, hMv⟩ := mem_ua1_iff.mp hMua
  have hxe : (xt : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k) ∈
      flagSpace 3 k 1 := by
    have h1 := hMv ((xt : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 2 1 : Fin 3 → k))
    have hinv : ((xt⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        (xt : Matrix (Fin 3) (Fin 3) k) = 1 := coe_inv_mul_coe xt
    have hMxt : (M : Matrix (Fin 3) (Fin 3) k) * (xt : Matrix (Fin 3) (Fin 3) k) =
        (xt : Matrix (Fin 3) (Fin 3) k) *
          ((uu (0 : k) 0 1 : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [hcoe]
      simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
    have h2 : (M : Matrix (Fin 3) (Fin 3) k) *ᵥ ((xt : Matrix (Fin 3) (Fin 3) k) *ᵥ
        (Pi.single 2 1 : Fin 3 → k)) = (xt : Matrix (Fin 3) (Fin 3) k) *ᵥ
        (((uu (0 : k) 0 1 : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
          (Pi.single 2 1 : Fin 3 → k)) := by
      rw [Matrix.mulVec_mulVec, hMxt, Matrix.mulVec_mulVec]
    have h3 : ((uu (0 : k) 0 1 : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
        (Pi.single 2 1 : Fin 3 → k) =
        (Pi.single 2 1 : Fin 3 → k) + (Pi.single 0 1 : Fin 3 → k) := by
      ext i
      fin_cases i <;> simp [coe_uu, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Pi.single_apply]
    rw [h2, h3, Matrix.mulVec_add, add_sub_cancel_left] at h1
    exact h1
  exact ⟨xt, mem_stabilizer_of_mulVec_mem hxe, rfl⟩

@[expose] def dg (l : kˣ) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨!![(l : k), 0, 0; 0, ((l⁻¹ : kˣ) : k), 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp [← Units.val_mul]⟩

theorem dg_mem_upperTriangular (l : kˣ) : (dg l : Matrix.SpecialLinearGroup (Fin 3) k) ∈
    upperTriangular 3 k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [dg, Fin.lt_def]

theorem dg_conj_uu (l : kˣ) (c : k) :
    dg l * uu 0 0 c * (dg l)⁻¹ = uu 0 0 ((l : k) * c) := by
  refine mul_inv_eq_iff_eq_mul.mpr ?_
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_conj_pzz {z z' : projectiveSL 3 k} (hz : z ∈ pzz k) (hz' : z' ∈ pzz k)
    (h1 : z ≠ 1) (h1' : z' ≠ 1) : ∃ b ∈ projUpperTriangular 3 k, b * z * b⁻¹ = z' := by
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hz
  obtain ⟨_, ⟨c', rfl⟩, rfl⟩ := hz'
  have hc : c ≠ 0 := by
    rintro rfl
    exact h1 (by rw [uu_zero, map_one])
  have hc' : c' ≠ 0 := by
    rintro rfl
    exact h1' (by rw [uu_zero, map_one])
  refine ⟨proj 3 k (dg (Units.mk0 (c' / c) (div_ne_zero hc' hc))),
    ⟨_, dg_mem_upperTriangular _, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, dg_conj_uu]
  congr 2
  simp [hc]

theorem card_pzz : Nat.card (pzz k) = Nat.card k := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : k =>
    (⟨proj 3 k (uu 0 0 c), ⟨uu 0 0 c, ⟨c, rfl⟩, rfl⟩⟩ : pzz k)) ⟨fun c c' h => ?_, ?_⟩)
  · have h1 : proj 3 k (uu 0 0 c) = proj 3 k (uu 0 0 c') := congrArg Subtype.val h
    have := proj_injOn_unitriangular 3 (uu_mem_unitriangular 0 0 c)
      (uu_mem_unitriangular 0 0 c') h1
    exact (uu_injective this).2.2
  · rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

end CFSG.Quasithin.E2.TI2b.L3
