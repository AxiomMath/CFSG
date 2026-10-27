module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix
open scoped commutatorElement

private def k328r6p_zmat (F : Type) [Field F] (ω : F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal fun k => if k = 3 then (1 : F) else ω

private theorem k328r6p_zmat_eq (F : Type) [Field F] (ω : F) :
    Matrix.diagonal ![ω, ω, ω, 1] = k328r6p_zmat F ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k328r6p_zmat, Matrix.diagonal]

private theorem k328r6p_omega_cube (F : Type) [Field F] (ω : F) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  have h2 : ω ^ 3 - 1 = 0 := by
    rw [show ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) by ring, hω, mul_zero]
  exact sub_eq_zero.mp h2

private theorem k328r6p_omega_ne_one (F : Type) [Field F] [CharP F 2] (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := by
    rw [h] at hω
    linear_combination hω
  have h3' : (3 : F) ≠ 0 := by
    intro h0
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h31 : (3 : F) = 2 + 1 := by norm_num
    rw [h31, h2, zero_add] at h0
    exact one_ne_zero h0
  exact h3' h3

private theorem k328r6p_block_of_commute (F : Type) [Field F] (ω : F) (hω : ω ≠ 1)
    (z₀ g : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * (z₀ : Matrix (Fin 4) (Fin 4) F) =
      (z₀ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) :
    ∀ i : Fin 4, i ≠ 3 →
      (g : Matrix (Fin 4) (Fin 4) F) i 3 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) 3 i = 0 := by
  intro i hi
  have e1 := congrFun (congrFun hg i) 3
  have e2 := congrFun (congrFun hg 3) i
  rw [hz, k328r6p_zmat, Matrix.mul_diagonal, Matrix.diagonal_mul] at e1 e2
  simp only [if_true] at e1 e2
  rw [if_neg hi] at e1 e2
  constructor
  · have h : (g : Matrix (Fin 4) (Fin 4) F) i 3 = ω * (g : Matrix (Fin 4) (Fin 4) F) i 3 := by
      simpa using e1
    have h' : (1 - ω) * (g : Matrix (Fin 4) (Fin 4) F) i 3 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hω))
  · have h : (g : Matrix (Fin 4) (Fin 4) F) 3 i * ω = (g : Matrix (Fin 4) (Fin 4) F) 3 i := by
      simpa using e2
    have h' : (g : Matrix (Fin 4) (Fin 4) F) 3 i * (ω - 1) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hω)

private theorem k328r6p_mem_statedSU_iff (F : Type) [Field F]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (n : ℕ) (hn : 1 ≤ n) (A : GL (Fin n) F) :
    A ∈ StatedSU n 8 F ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) F).map (· ^ (8 : ℕ)))ᵀ * (A : Matrix (Fin n) (Fin n) F) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F) (p := 2) (f := 3)
    Nat.prime_two hcard hn).1
  exact Set.ext_iff.mp h A

private theorem k328r6p_conjTr_eq (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) A =
      (A.map (· ^ (8 : ℕ)))ᵀ := by
  ext i j
  simp only [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply]
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
  norm_num

private theorem k328r6p_zmat_eq_blockMat (F : Type) [Field F] (ω : F) :
    k328r6p_zmat F ω =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (Matrix.diagonal fun _ : Fin 3 => ω) := by
  ext i j
  rw [k328r6p_zmat, CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal]

private theorem k328r6p_blockMat_comm_zmat (F : Type) [Field F] (ω : F)
    (A : Matrix (Fin 3) (Fin 3) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 0 A * k328r6p_zmat F ω =
      k328r6p_zmat F ω * CFSG.ClassicalInvolution.Phan.blockMat 4 0 A := by
  rw [k328r6p_zmat_eq_blockMat,
    ← CFSG.ClassicalInvolution.Phan.blockMat_mul (m := 4) (i := 0) (k := 3) (by norm_num),
    ← CFSG.ClassicalInvolution.Phan.blockMat_mul (m := 4) (i := 0) (k := 3) (by norm_num)]
  congr 1
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private theorem k328r6p_mem_H4_of_block (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) (B : GL (Fin 4) F) (A : GL (Fin 3) F)
    (hB : ((B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (A : Matrix (Fin 3) (Fin 3) F))
    (hA : A ∈ StatedSU 3 8 F) : B ∈ StatedSU 4 8 F := by
  obtain ⟨hdet, huni⟩ := (k328r6p_mem_statedSU_iff F hcard 3 (by norm_num) A).mp hA
  have hiff := k328r6p_mem_statedSU_iff F hcard 4 (by norm_num) B
  refine hiff.mpr ⟨?_, ?_⟩
  · rw [hB, CFSG.ClassicalInvolution.Phan.det_blockMat (m := 4) (i := 0) (k := 3) (by norm_num)]
    exact hdet
  · rw [hB, ← k328r6p_conjTr_eq, CFSG.ClassicalInvolution.Phan.conjTr_blockMat,
      ← CFSG.ClassicalInvolution.Phan.blockMat_mul (m := 4) (i := 0) (k := 3) (by norm_num)]
    have huni' : CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) (A : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [k328r6p_conjTr_eq]; exact huni
    rw [huni', CFSG.ClassicalInvolution.Phan.blockMat_one]

private theorem k328r6p_centralizer_of_block (F : Type) [Field F] (ω : F)
    (B : GL (Fin 4) F) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) (A : GL (Fin 3) F)
    (hB : ((B : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (A : Matrix (Fin 3) (Fin 3) F)) :
    B ∈ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, hB]
  exact k328r6p_blockMat_comm_zmat F ω (A : Matrix (Fin 3) (Fin 3) F)

private def k328r6p_C (F : Type) [Field F] (z₀ : GL (Fin 4) F) : Subgroup (GL (Fin 4) F) :=
  StatedSU 4 8 F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F))

private def k328r6p_ent {F : Type} [Field F] (g : GL (Fin 4) F) : F :=
  (g : Matrix (Fin 4) (Fin 4) F) 3 3

private theorem k328r6p_block_of_mem_C (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (g : k328r6p_C F z₀) :
    ∀ i : Fin 4, i ≠ 3 →
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i 3 = 0 ∧
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 i = 0 :=
  k328r6p_block_of_commute F ω hω z₀ (g : GL (Fin 4) F) hz
    (congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F))
      (Subgroup.mem_centralizer_singleton_iff.mp g.2.2))

private theorem k328r6p_ent_mul_33 (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (g h : k328r6p_C F z₀) :
    k328r6p_ent ((g * h : k328r6p_C F z₀) : GL (Fin 4) F) =
      k328r6p_ent (g : GL (Fin 4) F) * k328r6p_ent (h : GL (Fin 4) F) := by
  have hg := k328r6p_block_of_mem_C F ω hω z₀ hz g
  change ((((g : GL (Fin 4) F) * (h : GL (Fin 4) F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)) 3 3 =
    (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) 3 3 *
      (((h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) 3 3
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four]
  rw [(hg 0 (by decide)).2, (hg 1 (by decide)).2, (hg 2 (by decide)).2]
  simp

private theorem k328r6p_ent_33_ne_zero (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (g : k328r6p_C F z₀) : k328r6p_ent (g : GL (Fin 4) F) ≠ 0 := by
  intro h0
  have h1 : k328r6p_ent (((g * g⁻¹ : k328r6p_C F z₀) : GL (Fin 4) F)) = 1 := by
    rw [mul_inv_cancel]
    simp [k328r6p_ent]
  rw [k328r6p_ent_mul_33 F ω hω z₀ hz g g⁻¹, h0, zero_mul] at h1
  exact zero_ne_one h1

private noncomputable def k328r6p_rho (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) :
    k328r6p_C F z₀ →* Fˣ where
  toFun g := Units.mk0 (k328r6p_ent (g : GL (Fin 4) F))
    (k328r6p_ent_33_ne_zero F ω hω z₀ hz g)
  map_one' := by
    apply Units.ext
    simp [k328r6p_ent]
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    exact k328r6p_ent_mul_33 F ω hω z₀ hz g h

private theorem k328r6p_rho_apply (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (g : k328r6p_C F z₀) :
    ((k328r6p_rho F ω hω z₀ hz g : Fˣ) : F) = k328r6p_ent (g : GL (Fin 4) F) := rfl

private def k328r6p_J (F : Type) [Field F] (h03 : 0 + 3 ≤ 4) : Subgroup (GL (Fin 4) F) :=
  (StatedSU 3 8 F).map (CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03)

private theorem k328r6p_eq_blockMat_of_ker (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (g : k328r6p_C F z₀) (hg33 : k328r6p_ent (g : GL (Fin 4) F) = 1) :
    (g : GL (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0
        (Matrix.of fun i j : Fin 3 =>
          ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc) := by
  have hg := k328r6p_block_of_mem_C F ω hω z₀ hz g
  have hg33' : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := hg33
  let A : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc
  change ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    CFSG.ClassicalInvolution.Phan.blockMat 4 0 A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [CFSG.ClassicalInvolution.Phan.blockMat,
      CFSG.ClassicalInvolution.Phan.blockSel, Matrix.one_apply, Matrix.one_apply_ne,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp [A]

private theorem k328r6p_ker_elem_mem_J (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) (h03 : 0 + 3 ≤ 4)
    (g : k328r6p_C F z₀) (hg : k328r6p_rho F ω hω z₀ hz g = 1) :
    (g : GL (Fin 4) F) ∈ k328r6p_J F h03 := by
  have hg33 : k328r6p_ent (g : GL (Fin 4) F) = 1 := by
    rw [← k328r6p_rho_apply F ω hω z₀ hz g, hg, Units.val_one]
  let A : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc
  have hAeq : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 A :=
    k328r6p_eq_blockMat_of_ker F ω hω z₀ hz g hg33
  have hgmem := (k328r6p_mem_statedSU_iff F hcard 4 (by norm_num) (g : GL (Fin 4) F)).mp g.2.1
  have hdetA : A.det = 1 := by
    rw [← CFSG.ClassicalInvolution.Phan.det_blockMat (m := 4) (i := 0) (k := 3) (by norm_num),
      ← hAeq]
    exact hgmem.1
  have huniA : (A.map (· ^ (8 : ℕ)))ᵀ * A = 1 := by
    have h := hgmem.2
    rw [hAeq, ← k328r6p_conjTr_eq, CFSG.ClassicalInvolution.Phan.conjTr_blockMat,
      ← CFSG.ClassicalInvolution.Phan.blockMat_mul (m := 4) (i := 0) (k := 3) (by norm_num)] at h
    rw [← k328r6p_conjTr_eq]
    exact CFSG.ClassicalInvolution.Phan.blockMat_injective (by norm_num : 0 + 3 ≤ 4)
      (h.trans (CFSG.ClassicalInvolution.Phan.blockMat_one (F := F) (m := 4) (i := 0)
        (k := 3)).symm)
  let Ag : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact one_ne_zero)
  have hAgco : (Ag : Matrix (Fin 3) (Fin 3) F) = A := rfl
  have hAg : Ag ∈ StatedSU 3 8 F := by
    refine (k328r6p_mem_statedSU_iff F hcard 3 (by norm_num) Ag).mpr ⟨?_, ?_⟩
    · rw [hAgco]; exact hdetA
    · rw [hAgco]; exact huniA
  have hGL : (g : GL (Fin 4) F) = CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03 Ag := by
    apply Units.ext
    change ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (Ag : Matrix (Fin 3) (Fin 3) F)
    rw [hAgco]
    exact hAeq
  rw [hGL]
  exact Subgroup.mem_map_of_mem (CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03) hAg

private theorem k328r6p_commutator_le_J (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) (h03 : 0 + 3 ≤ 4) :
    ⁅k328r6p_C F z₀, k328r6p_C F z₀⁆ ≤ k328r6p_J F h03 := by
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  let aC : k328r6p_C F z₀ := ⟨a, ha⟩
  let bC : k328r6p_C F z₀ := ⟨b, hb⟩
  have hmem : ⁅a, b⁆ ∈ k328r6p_C F z₀ := by
    rw [commutatorElement_def]
    exact (k328r6p_C F z₀).mul_mem
      ((k328r6p_C F z₀).mul_mem ((k328r6p_C F z₀).mul_mem ha hb)
        ((k328r6p_C F z₀).inv_mem ha)) ((k328r6p_C F z₀).inv_mem hb)
  have hker : (⟨⁅a, b⁆, hmem⟩ : k328r6p_C F z₀) ∈
      (k328r6p_rho F ω hω z₀ hz).ker := by
    rw [MonoidHom.mem_ker]
    change (k328r6p_rho F ω hω z₀ hz) ⁅aC, bC⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact k328r6p_ker_elem_mem_J F hcard ω hω z₀ hz h03 ⟨⁅a, b⁆, hmem⟩
    (MonoidHom.mem_ker.mp hker)

private theorem k328r6p_J_le_C (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (_hω : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) (h03 : 0 + 3 ≤ 4) :
    k328r6p_J F h03 ≤ k328r6p_C F z₀ := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := hx
  have hB : ((CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03 A : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (A : Matrix (Fin 3) (Fin 3) F) :=
    CFSG.ClassicalInvolution.Phan.coe_blockGL h03 A
  refine ⟨k328r6p_mem_H4_of_block F hcard _ A hB hA, ?_⟩
  exact k328r6p_centralizer_of_block F ω _ z₀ hz A hB

private theorem k328r6p_J_le_commutator (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ≠ 1)
    (z₀ : GL (Fin 4) F) (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (h03 : 0 + 3 ≤ 4) :
    k328r6p_J F h03 ≤ ⁅k328r6p_C F z₀, k328r6p_C F z₀⁆ := by
  have hperf33 : Group.IsPerfect (StatedSU 3 8 F : Subgroup (GL (Fin 3) F)) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := 3)
      (n := 3) hcard le_rfl (by decide)).1.1
  have hJperf : Group.IsPerfect (k328r6p_J F h03 : Subgroup (GL (Fin 4) F)) := by
    rw [k328r6p_J]
    exact @Group.IsPerfect.map _ _ _ _ (StatedSU 3 8 F)
      (CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03) hperf33
  have hJJ : ⁅k328r6p_J F h03, k328r6p_J F h03⁆ = k328r6p_J F h03 :=
    Subgroup.isPerfect_iff.mp hJperf
  calc k328r6p_J F h03 = ⁅k328r6p_J F h03, k328r6p_J F h03⁆ := hJJ.symm
    _ ≤ ⁅k328r6p_C F z₀, k328r6p_C F z₀⁆ :=
      Subgroup.commutator_mono (k328r6p_J_le_C F hcard ω hω z₀ hz h03)
        (k328r6p_J_le_C F hcard ω hω z₀ hz h03)

private theorem k328r6p_stdComp_eq (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ≠ 1)
    (z₀ : GL (Fin 4) F) (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (h03 : 0 + 3 ≤ 4) :
    stdComp (StatedSU 4 8 F) z₀ = k328r6p_J F h03 := by
  unfold stdComp
  show ⁅StatedSU 4 8 F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F)),
      StatedSU 4 8 F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F))⁆ = k328r6p_J F h03
  exact le_antisymm (k328r6p_commutator_le_J F hcard ω hω z₀ hz h03)
    (k328r6p_J_le_commutator F hcard ω hω z₀ hz h03)

private theorem k328r6p_blockGL_injective (F : Type) [Field F] (h03 : 0 + 3 ≤ 4) :
    Function.Injective (CFSG.ClassicalInvolution.Phan.blockGL (F := F) (k := 3) 4 0 h03) := by
  intro A B hAB
  apply Units.ext
  exact CFSG.ClassicalInvolution.Phan.blockMat_injective h03
    (congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hAB)

private noncomputable def k328r6p_J_equiv (F : Type) [Field F] (h03 : 0 + 3 ≤ 4) :
    ↥(k328r6p_J F h03) ≃* ↥(StatedSU 3 8 F) :=
  (Subgroup.equivMapOfInjective (StatedSU 3 8 F)
    (CFSG.ClassicalInvolution.Phan.blockGL (F := F) (k := 3) 4 0 h03)
    (k328r6p_blockGL_injective F h03)).symm

private theorem k328r6p_J_le_H (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (h03 : 0 + 3 ≤ 4) :
    k328r6p_J F h03 ≤ StatedSU 4 8 F := by
  rw [k328r6p_J]
  rintro _ ⟨A, hA, rfl⟩
  have hB : ((CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03 A : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 (A : Matrix (Fin 3) (Fin 3) F) :=
    CFSG.ClassicalInvolution.Phan.coe_blockGL h03 A
  exact k328r6p_mem_H4_of_block F hcard _ A hB hA

private theorem k328r6p_orderOf_z0 (F : Type) [Field F] (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) : orderOf z₀ = 3 := by
  have hωc := k328r6p_omega_cube F ω hω
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hz, k328r6p_zmat, diagonal_pow]
    change Matrix.diagonal ((fun k : Fin 4 => if k = 3 then 1 else ω) ^ 3) = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp_all
  · intro h
    have h00 : (z₀ : Matrix (Fin 4) (Fin 4) F) 0 0 =
        (1 : Matrix (Fin 4) (Fin 4) F) 0 0 := by rw [h]; rfl
    rw [hz, k328r6p_zmat] at h00
    simp [Matrix.diagonal] at h00
    exact hω1 h00

private theorem k328r6p_z0_mem_J (F : Type) [Field F] [Fact (Nat.Prime 2)] [CharP F 2]
    (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (_hω1 : ω ≠ 1)
    (z₀ : GL (Fin 4) F) (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω)
    (h03 : 0 + 3 ≤ 4) : z₀ ∈ k328r6p_J F h03 := by
  have hωc : ω ^ 3 = 1 := k328r6p_omega_cube F ω hω
  have hω0 : ω ≠ 0 := by
    intro h; rw [h] at hωc; norm_num at hωc
  let ωu : Fˣ := Units.mk0 ω hω0
  let zA : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) ωu
  have hωcu : ωu ^ 3 = 1 := by
    apply Units.ext
    change (ω : F) ^ 3 = ((1 : Fˣ) : F)
    rw [Units.val_one]
    exact hωc
  have hω9 : ωu ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by norm_num, pow_mul, hωcu, one_pow]
  have hzA : zA ∈ StatedSU 3 8 F :=
    (CFSG.LinearGroups.scalar_mem_statedSU_iff (K := F) (p := 2) (f := 3) Nat.prime_two
      hcard (n := 3) (by norm_num) ωu).mpr ⟨hωcu, hω9⟩
  have hGLz : z₀ = CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03 zA := by
    apply Units.ext
    rw [hz, k328r6p_zmat_eq_blockMat]
    rfl
  rw [hGLz]
  exact Subgroup.mem_map_of_mem (CFSG.ClassicalInvolution.Phan.blockGL (k := 3) 4 0 h03) hzA

private theorem k328r6p_centralizer_zpowers_eq (F : Type) [Field F] (z₀ : GL (Fin 4) F)
    (hz₀ : z₀ ∈ StatedSU 4 8 F) :
    Subgroup.centralizer (Subgroup.zpowers (⟨z₀, hz₀⟩ : StatedSU 4 8 F) :
      Set (StatedSU 4 8 F)) = (k328r6p_C F z₀).subgroupOf (StatedSU 4 8 F) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  ext y
  change (y ∈ Subgroup.centralizer ({⟨z₀, hz₀⟩} : Set (StatedSU 4 8 F))) ↔
    (y : GL (Fin 4) F) ∈ StatedSU 4 8 F ⊓
      Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F))
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    exact ⟨y.2, congrArg (fun x : StatedSU 4 8 F => (x : GL (Fin 4) F)) hy⟩
  · rintro ⟨-, hc⟩
    apply Subtype.ext
    exact hc

private theorem k328r6p_center_SU3 (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) :
    Nat.card (Subgroup.center (StatedSU 3 8 F : Subgroup (GL (Fin 3) F))) = 3 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := 3)
    (n := 3) hcard le_rfl (by decide)).2]
  rw [(CFSG.LinearGroups.unitary_scalar_kernel (K := F) (p := 2) (f := 3) Nat.prime_two hcard
    (n := 3) (by norm_num)).2.2]
  norm_num

private theorem k328r6p_lieModel_SU3 (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) :
    CFSG.Blueprint.LieModel
      (↥(StatedSU 3 8 F : Subgroup (GL (Fin 3) F)) ⧸
        Subgroup.center ↥(StatedSU 3 8 F)) .PSU 3 2 3 := by
  have hcenter : Subgroup.center ↥(StatedSU 3 8 F) =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 8 F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := 3)
      (n := 3) hcard le_rfl (by decide)).2
  have hadm : StatedLieAdmissible .PSU 3 2 3 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
  refine Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
  exact QuotientGroup.quotientMulEquivOfEq hcenter

private theorem k328r6p_rho_eq_one_iff (F : Type) [Field F] [Finite F] [Fact (Nat.Prime 2)]
    [CharP F 2] (hcard : Nat.card F = (2 ^ 3) ^ 2) (ω : F) (hω : ω ≠ 1)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω) (h03 : 0 + 3 ≤ 4)
    (g : k328r6p_C F z₀) :
    k328r6p_rho F ω hω z₀ hz g = 1 ↔ (g : GL (Fin 4) F) ∈ k328r6p_J F h03 := by
  constructor
  · exact k328r6p_ker_elem_mem_J F hcard ω hω z₀ hz h03 g
  · intro hg
    have hstd : stdComp (StatedSU 4 8 F) z₀ = k328r6p_J F h03 :=
      k328r6p_stdComp_eq F hcard ω hω z₀ hz h03
    have hJCC : k328r6p_J F h03 = ⁅k328r6p_C F z₀, k328r6p_C F z₀⁆ := hstd.symm
    rw [hJCC] at hg
    have htop : ⁅(⊤ : Subgroup ↥(k328r6p_C F z₀)), ⊤⁆ ≤
        (k328r6p_rho F ω hω z₀ hz).ker := by
      refine Subgroup.commutator_le.mpr ?_
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have hmap : ⁅k328r6p_C F z₀, k328r6p_C F z₀⁆ ≤
        (k328r6p_rho F ω hω z₀ hz).ker.map (k328r6p_C F z₀).subtype := by
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.map_mono htop
    obtain ⟨k, hk1, hk2⟩ := hmap hg
    have hkg : k = g := Subtype.ext hk2
    rw [← hkg]
    exact hk1

private theorem k328r6p_row6_pos_general (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (Nat.Prime 2)] [CharP F 2]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    PosLeaf (StatedSU 4 8 F) z₀ := by
  intro hz₀
  have _ := ht
  have hcard : Nat.card F = (2 ^ 3) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF]; norm_num
  have hω1 : ω ≠ 1 := k328r6p_omega_ne_one F ω hω
  have hz' : (z₀ : Matrix (Fin 4) (Fin 4) F) = k328r6p_zmat F ω := by
    rw [hz, k328r6p_zmat_eq]
  have h03 : 0 + 3 ≤ 4 := by norm_num
  have hstd : stdComp (StatedSU 4 8 F) z₀ = k328r6p_J F h03 :=
    k328r6p_stdComp_eq F hcard ω hω1 z₀ hz' h03
  have ho : orderOf z₀ = 3 := k328r6p_orderOf_z0 F ω hω hω1 z₀ hz'
  have hzJ : z₀ ∈ k328r6p_J F h03 := k328r6p_z0_mem_J F hcard ω hω hω1 z₀ hz' h03
  have hCL : Subgroup.centralizer
      (Subgroup.zpowers (⟨z₀, hz₀⟩ : StatedSU 4 8 F) : Set (StatedSU 4 8 F)) =
      (k328r6p_C F z₀).subgroupOf (StatedSU 4 8 F) :=
    k328r6p_centralizer_zpowers_eq F z₀ hz₀
  have hJH : k328r6p_J F h03 ≤ StatedSU 4 8 F := k328r6p_J_le_H F hcard h03
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨z₀, hz₀⟩ : StatedSU 4 8 F)]
    exact ho
  · rw [hstd, Subgroup.zpowers_le]; exact Subgroup.mem_subgroupOf.mpr hzJ
  · rw [hstd, hCL]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact k328r6p_J_le_C F hcard ω hω1 z₀ hz' h03 hx
  · rw [hstd, hCL]
    let D : Subgroup ↥(StatedSU 4 8 F) := (k328r6p_C F z₀).subgroupOf (StatedSU 4 8 F)
    let eC : ↥D ≃* ↥(k328r6p_C F z₀) := Subgroup.subgroupOfEquivOfLe inf_le_left
    have hmap : (((k328r6p_J F h03).subgroupOf (StatedSU 4 8 F)).subgroupOf D) =
        ((k328r6p_rho F ω hω1 z₀ hz').comp eC.toMonoidHom).ker := by
      ext d
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [k328r6p_rho_eq_one_iff F hcard ω hω1 z₀ hz' h03 (eC d)]
      rfl
    rw [hmap]
    exact (inferInstance :
      ((k328r6p_rho F ω hω1 z₀ hz').comp eC.toMonoidHom).ker.Normal).isSubnormal
  · rw [hstd]
    have e : ↥((k328r6p_J F h03).subgroupOf (StatedSU 4 8 F)) ≃* ↥(StatedSU 3 8 F) :=
      (Subgroup.subgroupOfEquivOfLe hJH).trans (k328r6p_J_equiv F h03)
    have hq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (F := F) (p := 2) (f := 3) (n := 3) hcard le_rfl (by decide)).1
    exact isQuasisimple_of_mulEquiv' e.symm ⟨hq.1.1, hq.2.1⟩
  · rw [hstd]
    have e : ↥((k328r6p_J F h03).subgroupOf (StatedSU 4 8 F)) ≃* ↥(StatedSU 3 8 F) :=
      (Subgroup.subgroupOfEquivOfLe hJH).trans (k328r6p_J_equiv F h03)
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans (k328r6p_center_SU3 F hcard)
  · rw [hstd]
    have e : ↥((k328r6p_J F h03).subgroupOf (StatedSU 4 8 F)) ≃* ↥(StatedSU 3 8 F) :=
      (Subgroup.subgroupOfEquivOfLe hJH).trans (k328r6p_J_equiv F h03)
    have qe := QuotientGroup.congr
      (Subgroup.center ↥((k328r6p_J F h03).subgroupOf (StatedSU 4 8 F)))
      (Subgroup.center ↥(StatedSU 3 8 F)) e (Subgroup.map_center_eq e)
    exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv qe.symm (k328r6p_lieModel_SU3 F hcard))

theorem row6_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    PosLeaf (StatedSU 4 8 F) z₀ :=
  @k328r6p_row6_pos_general F _ _ _ ⟨Nat.prime_two⟩
    (charP_of_card_eq_prime_pow (p := 2) (f := 6) (by rw [hF]; norm_num))
    hF ω hω z₀ t₀ hz ht

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
