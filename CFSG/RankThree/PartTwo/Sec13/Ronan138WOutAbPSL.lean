module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterLin
import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbCube

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138W

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {K : Type} [Field K] [Finite K]

theorem ringAut_comm_of_finite (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic hℓ K hK
  exact IsMulCommutative.is_comm.comm σ τ

theorem exists_conjAut_fieldAut_of_pow {α : MulAut (projectiveSL 3 K)} {k : ℕ}
    (hα : α ^ 3 ^ k = 1) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), σ ^ 3 ^ k = 1 ∧ α = conjAut 3 K A * fieldAut 3 K σ := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    refine ⟨A, σ, ?_, rfl⟩
    have hpow : ∀ j : ℕ, ∃ B : GL (Fin 3) K,
        (conjAut 3 K A * fieldAut 3 K σ) ^ j = conjAut 3 K B * fieldAut 3 K (σ ^ j) := by
      intro j
      induction j with
      | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, mul_one]⟩
      | succ j ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨B * GeneralLinearGroup.map ((σ ^ j : K ≃+* K) : K →+* K) A, ?_⟩
        rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]
    obtain ⟨B, hB⟩ := hpow (3 ^ k)
    rw [hα] at hB
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B _ hB.symm).1
  · exfalso
    rw [pow_one] at hα
    set e := conjAut 3 K A * fieldAut 3 K σ with he
    have heE : e ∈ semilinearAutGroup 3 K := mem_semilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
    have hδδ : dualAut 3 K * dualAut 3 K = 1 :=
      (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
    have heven : ∀ j : ℕ, (e * dualAut 3 K) ^ (2 * j) ∈ semilinearAutGroup 3 K := by
      intro j
      induction j with
      | zero => rw [mul_zero, pow_zero]; exact one_mem _
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, pow_two]
        have h2 : e * dualAut 3 K * (e * dualAut 3 K) =
            e * (dualAut 3 K * e * dualAut 3 K) := by group
        rw [h2]
        exact mul_mem ih (mul_mem heE (dualAut_mul_mul_dualAut_mem heE))
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hj, pow_succ] at hα
    have hδ : dualAut 3 K = ((e * dualAut 3 K) ^ (2 * j) * e)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [mul_assoc]
      exact hα
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
      (K := K) le_rfl (hδ ▸ inv_mem (mul_mem (heven j) heE))

theorem conjAut_mem_range_conj_of_cube {C : GL (Fin 3) K} {c : Kˣ}
    (hc : c ^ 3 = GeneralLinearGroup.det C) :
    conjAut 3 K C ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  set D : GL (Fin 3) K := C * GeneralLinearGroup.scalar (Fin 3) c⁻¹ with hD
  have hdet : GeneralLinearGroup.det D = 1 := by
    rw [hD, map_mul, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow,
      mul_inv_cancel]
  set s : SpecialLinearGroup (Fin 3) K := ⟨(D : Matrix (Fin 3) (Fin 3) K), by
    have := congrArg Units.val hdet
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩ with hs
  refine ⟨proj 3 K s, ?_⟩
  rw [CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut]
  have hsD : SpecialLinearGroup.toGL s = D := Units.ext rfl
  rw [hsD, hD, map_mul]
  have h1 : conjAut 3 K (GeneralLinearGroup.scalar (Fin 3) c⁻¹) = 1 :=
    (CFSG.RankThree.PartTwo.Sec4.RonanK432.L3Outer.conjAut_eq_one_iff _).mpr
      (CFSG.RankThree.PartTwo.Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨c⁻¹, rfl⟩)
  rw [h1, mul_one]

theorem det_map (σ : K ≃+* K) (B : GL (Fin 3) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) B) =
      Units.map (σ : K →* K) (GeneralLinearGroup.det B) := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (σ : K →+* K) _).symm

theorem exists_cube_eq_map_mul_inv {σ : K ≃+* K} {k : ℕ} (hσ : σ ^ 3 ^ k = 1) (b : Kˣ) :
    ∃ c : Kˣ, c ^ 3 = Units.map (σ : K →* K) b * b⁻¹ := by
  refine exists_cube_eq_mul_inv_of_cyclic (Units.map (σ : K →* K)) (fun y hy => ?_) b
  apply Units.ext
  rw [Units.coe_map]
  have h := congrArg Units.val hy
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h
  exact apply_eq_of_pow_three_eq_one hσ h

theorem comm_mem_range_conj_of_pow {α β : MulAut (projectiveSL 3 K)} {a b : ℕ}
    (hα : α ^ 3 ^ a = 1) (hβ : β ^ 3 ^ b = 1) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨A, σ, hσ, rfl⟩ := exists_conjAut_fieldAut_of_pow hα
  obtain ⟨B, τ, hτ, rfl⟩ := exists_conjAut_fieldAut_of_pow hβ
  have h1 := conjAut_mul_fieldAut_mul (n := 3) (K := K) A B σ τ
  have h2 := conjAut_mul_fieldAut_mul (n := 3) (K := K) B A τ σ
  rw [ringAut_comm_of_finite τ σ] at h2
  have e1 : conjAut 3 K A * fieldAut 3 K σ * (conjAut 3 K B * fieldAut 3 K τ) *
      (conjAut 3 K A * fieldAut 3 K σ)⁻¹ * (conjAut 3 K B * fieldAut 3 K τ)⁻¹ =
      (conjAut 3 K A * fieldAut 3 K σ * (conjAut 3 K B * fieldAut 3 K τ)) *
        (conjAut 3 K B * fieldAut 3 K τ * (conjAut 3 K A * fieldAut 3 K σ))⁻¹ := by group
  have e2 : conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K) B) * fieldAut 3 K (σ * τ) *
      (conjAut 3 K (B * GeneralLinearGroup.map (τ : K →+* K) A) * fieldAut 3 K (σ * τ))⁻¹ =
      conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K) B) *
        (conjAut 3 K (B * GeneralLinearGroup.map (τ : K →+* K) A))⁻¹ := by group
  rw [e1, h1, h2, e2, ← map_inv, ← map_mul]
  obtain ⟨c₁, hc₁⟩ := exists_cube_eq_map_mul_inv hσ (GeneralLinearGroup.det B)
  obtain ⟨c₂, hc₂⟩ := exists_cube_eq_map_mul_inv hτ (GeneralLinearGroup.det A)
  refine conjAut_mem_range_conj_of_cube (c := c₁ * c₂⁻¹) ?_
  rw [mul_pow, inv_pow, hc₁, hc₂, map_mul, map_inv, map_mul, map_mul, det_map, det_map]
  simp only [_root_.mul_inv_rev, inv_inv, mul_comm, mul_left_comm, mul_assoc]

end CFSG.RankThree.PartTwo.Sec13.Ronan138W
