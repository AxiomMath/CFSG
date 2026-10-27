module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoFixedPointFree
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorusDiag
public import CFSG.LargeExtraspecial.OutSix
public import CFSG.GF2Type.ModelPSU
public import CFSG.Open.StatedSUFieldChange
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Assembly.GL83StatedBridge
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

variable (K) in
@[expose] def torSU : Subgroup ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  (TauCeti.diagonalTorus K 6).comap (LargeEvenSUGroup (Fin 6) K (2 ^ 1)).subtype

variable (K) in
@[expose] def torU : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  (torSU K).map (LargeEvenProjMk _)

theorem fieldDataFour (hK : Nat.card K = 4) : UnitaryFieldData 2 1 K where
  prime := Nat.prime_two
  one_le := le_rfl
  card := by simpa using hK

theorem fieldDataFour_bar (hK : Nat.card K = 4) (x : K) :
    (fieldDataFour hK).bar x = x ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

theorem charP_two_of_card_four (hK : Nat.card K = 4) : CharP K 2 :=
  (fieldDataFour hK).charP

theorem four_eq_zero (hK : Nat.card K = 4) : (4 : K) = 0 := by
  haveI := charP_two_of_card_four hK
  exact (CharP.cast_eq_zero_iff K 2 4).mpr (by norm_num)

theorem two_eq_zero (hK : Nat.card K = 4) : (2 : K) = 0 := by
  haveI := charP_two_of_card_four hK
  exact (CharP.cast_eq_zero_iff K 2 2).mpr dvd_rfl

theorem one_add_one_eq_zero (hK : Nat.card K = 4) : (1 : K) + 1 = 0 := by
  linear_combination two_eq_zero hK

theorem neg_one_eq_one (hK : Nat.card K = 4) : (-1 : K) = 1 :=
  neg_eq_of_add_eq_zero_left (one_add_one_eq_zero hK)

theorem cube_unit_eq_one [Finite K] (hK : Nat.card K = 4) (t : Kˣ) : t ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  have := pow_card_eq_one' (G := Kˣ) (x := t)
  rwa [h3] at this

theorem exists_unit_ne_one [Finite K] (hK : Nat.card K = 4) : ∃ t : Kˣ, t ≠ 1 := by
  by_contra h
  push Not at h
  haveI : Subsingleton Kˣ := ⟨fun a b => by rw [h a, h b]⟩
  have h1 : Nat.card Kˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [Nat.card_units, hK] at h1
  norm_num at h1

theorem exists_root_omega [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨t, ht⟩ := exists_unit_ne_one hK
  have h3 : t ^ 3 = 1 := cube_unit_eq_one hK t
  refine ⟨(t : K), ?_⟩
  have hval : (t : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3]; rfl
  have hfac : ((t : K) - 1) * ((t : K) ^ 2 + (t : K) + 1) = 0 := by
    linear_combination hval
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    apply ht
    exact Units.ext (sub_eq_zero.mp h)
  · exact h

section Omega

variable [Finite K] {ω : K}

theorem omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h; rw [h] at hω; norm_num at hω

theorem omega_cube (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem omega_ne_one (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have h2 := two_eq_zero hK
  have hone : (1 : K) = 0 := by
    linear_combination hω - h2
  exact one_ne_zero hone

theorem omega_sq_ne_omega (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 ≠ ω := by
  intro h
  have h2 := two_eq_zero hK
  have hone : (1 : K) = 0 := by
    linear_combination hω - h - ω * h2
  exact one_ne_zero hone

theorem omega_sq_ne_one (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 ≠ 1 := by
  intro h
  apply omega_ne_one hK hω
  calc ω = 1 * ω := (one_mul ω).symm
    _ = ω ^ 2 * ω := by rw [h]
    _ = ω ^ 3 := by ring
    _ = 1 := omega_cube hω

theorem omega_add_sq (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) :
    ω + ω ^ 2 = 1 := by
  have hneg := neg_one_eq_one hK
  linear_combination hω + hneg

theorem eq_zero_or_one_or_omega_or_sq (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (x : K) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hfour : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : x ^ 4 = x := by
    have h := FiniteField.pow_card (K := K) x
    rwa [hfour] at h
  have h4 : x * (x ^ 3 - 1) = 0 := by linear_combination hpow
  rcases mul_eq_zero.mp h4 with hx0 | hx3
  · exact Or.inl hx0
  · right
    have hx3' : x ^ 3 = 1 := sub_eq_zero.mp hx3
    have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3'
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · right
      have hfac2 : (x - ω) * (x - ω ^ 2) = 0 := by
        linear_combination h2 - x * hω + (ω - 1) * hω
      rcases mul_eq_zero.mp hfac2 with h3 | h3
      · exact Or.inl (sub_eq_zero.mp h3)
      · exact Or.inr (sub_eq_zero.mp h3)

theorem ringEquiv_fixes_all (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {φ : K ≃+* K} (hφ : φ ω = ω) : φ = RingEquiv.refl K := by
  ext x
  rcases eq_zero_or_one_or_omega_or_sq hK hω x with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact hφ
  · rw [map_pow, hφ]; rfl

theorem ringEquiv_fixes_one_or_swaps (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {φ : K ≃+* K} : φ ω = ω ∨ φ ω = ω ^ 2 := by
  set x := φ ω
  have hx : x ^ 2 + x + 1 = 0 := by simpa [x] using congrArg φ hω
  have hfac : (x - ω) * (x - ω ^ 2) = 0 := by
    linear_combination hx - x * hω + (ω - 1) * hω
  rcases mul_eq_zero.mp hfac with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

end Omega

section Diag

variable [Finite K] {ω : K} {i j : Fin 6}

@[expose] noncomputable def diagVec (ω : K) (i j : Fin 6) : Fin 6 → K :=
  Function.update (Function.update (1 : Fin 6 → K) i ω) j (ω ^ 2)

theorem diagVec_self (hij : i ≠ j) : diagVec ω i j i = ω := by
  simp [diagVec, Function.update, hij]

theorem diagVec_other (hij : i ≠ j) : diagVec ω i j j = ω ^ 2 := by
  simp [diagVec, Function.update]

theorem diagVec_of_ne {k : Fin 6} (hki : k ≠ i) (hkj : k ≠ j) :
    diagVec ω i j k = 1 := by
  simp [diagVec, Function.update, hki, hkj]

theorem diagVec_cube (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) (k : Fin 6) :
    diagVec ω i j k ^ 3 = 1 := by
  by_cases hki : k = i
  · subst hki; rw [diagVec_self hij, omega_cube hω]
  · by_cases hkj : k = j
    · subst hkj; rw [diagVec_other hij]
      rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, omega_cube hω, one_pow]
    · rw [diagVec_of_ne hki hkj, one_pow]

theorem diagVec_prod (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ∏ k, diagVec ω i j k = 1 := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ j)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (s := (Finset.univ : Finset (Fin 6)) \ {j})
    (i := i) (by simp [hij])]
  have hrest : ∀ k ∈ (((Finset.univ : Finset (Fin 6)) \ {j}) \ {i}),
      diagVec ω i j k = 1 := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hk
    exact diagVec_of_ne hk.2 hk.1
  rw [Finset.prod_eq_one hrest, diagVec_other hij, diagVec_self hij, mul_one,
    ← pow_succ, omega_cube hω]

theorem diagVec_sum (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ∑ k, diagVec ω i j k = 1 := by
  classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (s := (Finset.univ : Finset (Fin 6)) \ {j})
    (i := i) (by simp [hij])]
  have hset : (((Finset.univ : Finset (Fin 6)) \ {j}) \ {i}) =
      (Finset.univ.erase j).erase i := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and,
      Finset.mem_erase]
    tauto
  have hrest : ∑ k ∈ (((Finset.univ : Finset (Fin 6)) \ {j}) \ {i}),
      diagVec ω i j k = 4 := by
    rw [hset]
    have hcongr : ∀ k ∈ (Finset.univ.erase j).erase i, diagVec ω i j k = 1 := by
      intro k hk
      rw [Finset.mem_erase, Finset.mem_erase] at hk
      exact diagVec_of_ne hk.1 hk.2.1
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩),
      Finset.card_erase_of_mem (by simp)]
    norm_num
  rw [hrest, diagVec_other hij, diagVec_self hij, four_eq_zero hK, add_zero, add_comm,
    omega_add_sq hK hω]

@[expose] noncomputable def diagTwo (ω : K) (i j : Fin 6) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal (diagVec ω i j)

theorem diagTwo_det (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    (diagTwo ω i j).det = 1 := by
  rw [diagTwo, Matrix.det_diagonal, diagVec_prod hω hij]

theorem diagTwo_unitary (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ((diagTwo ω i j).map (· ^ 2))ᵀ * diagTwo ω i j = 1 := by
  rw [diagTwo, Matrix.diagonal_map (by norm_num), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
  funext k
  rw [show diagVec ω i j k ^ 2 * diagVec ω i j k = diagVec ω i j k ^ 3 by ring,
    diagVec_cube hω hij k]
  rfl

@[expose] noncomputable def diagTwoGL (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagTwo ω i j) (by
    rw [diagTwo_det hω hij]; exact one_ne_zero)

theorem diagTwoGL_mem_SU (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    diagTwoGL hω hij ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact diagTwo_det hω hij
  · rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact diagTwo_unitary hω hij

@[expose] noncomputable def diagTwoSU (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨diagTwoGL hω hij, diagTwoGL_mem_SU hω hij⟩

theorem coe_diagTwoSU (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ((diagTwoSU hω hij : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) =
      diagTwoGL hω hij := rfl

theorem coe_diagTwoSU_matrix (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    (((diagTwoSU hω hij : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagTwo ω i j := by
  rw [coe_diagTwoSU, diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem diagTwoSU_mem_torSU (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    diagTwoSU hω hij ∈ torSU K := by
  rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
  show (((diagTwoSU hω hij : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) : GL (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K).IsDiag
  rw [coe_diagTwoSU_matrix]
  exact Matrix.isDiag_diagonal _

@[expose] noncomputable def diagTwoTor (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) : torSU K :=
  ⟨diagTwoSU hω hij, diagTwoSU_mem_torSU hω hij⟩

theorem coe_diagTwoTor (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ((diagTwoTor hω hij : torSU K) : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
      diagTwoSU hω hij := rfl

theorem diagTwoTor_matrix (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    ((((diagTwoTor hω hij : torSU K) : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagTwo ω i j := by
  exact coe_diagTwoSU_matrix hω hij

theorem trace_diagTwo (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0) (hij : i ≠ j) :
    (diagTwo ω i j).trace = 1 := by
  rw [diagTwo, Matrix.trace_diagonal, diagVec_sum hK hω hij]

end Diag

section SU

variable [Finite K]

theorem mem_SU_iff (h : UnitaryFieldData 2 1 K) {A : GL (Fin 6) K} :
    A ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) ↔
      (A : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        ((A : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ *
          (A : Matrix (Fin 6) (Fin 6) K) = 1 := by
  rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU,
    CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU h,
    CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU]
  rw [Units.val_one, Matrix.mul_one]
  exact and_comm

end SU

section Scalar

variable [Finite K]

theorem diagonal_map_transpose_mul_eq_one (v : Fin 6 → K) (hv : ∀ i, v i ^ 3 = 1) :
    ((Matrix.diagonal v).map (· ^ 2))ᵀ * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (by norm_num), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_eq_one]
  funext k
  rw [show v k ^ 2 * v k = v k ^ 3 by ring, hv k]
  rfl

theorem diagGL_map_transpose_mul_eq_one (hK : Nat.card K = 4) (t : Fin 6 → Kˣ) :
    (((TauCeti.diagGL t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map (· ^ 2))ᵀ *
      ((TauCeti.diagGL t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
  rw [TauCeti.diagGL_coe]
  exact diagonal_map_transpose_mul_eq_one (fun i => (t i : K)) (fun i => by
    rw [← Units.val_pow_eq_pow_val, cube_unit_eq_one hK (t i)]
    rfl)

theorem scalar_mem_SU (hK : Nat.card K = 4) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  apply Subgroup.subset_closure
  constructor
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const]
    have hc : (c : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, cube_unit_eq_one hK c]
      rfl
    have h6 : (c : K) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hc, one_pow]
    simpa using h6
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact diagonal_map_transpose_mul_eq_one (fun _ => (c : K)) (fun _ => by
      rw [← Units.val_pow_eq_pow_val, cube_unit_eq_one hK c]
      rfl)

theorem scalars_le_SU (hK : Nat.card K = 4) :
    LargeEvenScalars (Fin 6) K ≤ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  rintro x ⟨c, rfl⟩
  exact scalar_mem_SU hK c

theorem scalars_subgroupOf_le_torSU (hK : Nat.card K = 4) :
    (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≤
      torSU K := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
  obtain ⟨c, hc⟩ := hx
  show (((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).IsDiag
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact Matrix.isDiag_diagonal _

theorem card_scalars (hK : Nat.card K = 4) :
    Nat.card (LargeEvenScalars (Fin 6) K) = 3 := by
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun g : GL (Fin 6) K =>
      ((g : Matrix (Fin 6) (Fin 6) K)) 0 0) hab
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup Kˣ)) (f :=
    (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K)) hinj
  rw [Subgroup.map_top, Subgroup.card_top, Nat.card_units, hK] at h
  exact h

theorem card_scalars_subgroupOf_SU (hK : Nat.card K = 4) :
    Nat.card ((LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 3 := by
  have h := Subgroup.card_subtype (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
    ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (scalars_le_SU hK)] at h
  rw [← h, card_scalars hK]

end Scalar

section Card

variable [Finite K]

@[expose] noncomputable def diagTorusDet (K : Type) [Field K] :
    ↥(TauCeti.diagonalTorus K 6) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp (TauCeti.diagonalTorus K 6).subtype

theorem prod_update_one (i : Fin 6) (u : Kˣ) :
    ∏ k, Function.update (1 : Fin 6 → Kˣ) i u k = u := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i)]
  have hrest : ∀ k ∈ (Finset.univ : Finset (Fin 6)) \ {i},
      Function.update (1 : Fin 6 → Kˣ) i u k = 1 := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hk
    simp [Function.update, hk]
  rw [Finset.prod_eq_one hrest, mul_one]
  simp [Function.update]

theorem diagTorusDet_surjective :
    Function.Surjective (diagTorusDet K) := by
  intro u
  refine ⟨(TauCeti.diagonalTorusEquiv K 6) (Function.update (1 : Fin 6 → Kˣ) 0 u), ?_⟩
  rw [diagTorusDet, MonoidHom.comp_apply]
  change Matrix.GeneralLinearGroup.det
    (((TauCeti.diagonalTorusEquiv K 6) (Function.update (1 : Fin 6 → Kˣ) 0 u) :
      TauCeti.diagonalTorus K 6) : GL (Fin 6) K) = u
  rw [TauCeti.coe_diagonalTorusEquiv_apply, TauCeti.det_diagGL, prod_update_one]

theorem diagTorusDet_ker (hK : Nat.card K = 4) :
    (diagTorusDet K).ker =
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1)).subgroupOf (TauCeti.diagonalTorus K 6) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    rw [mem_SU_iff (fieldDataFour hK)]
    have hdet : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      have h := congrArg Units.val hx
      rw [diagTorusDet, MonoidHom.comp_apply] at h
      rw [Matrix.GeneralLinearGroup.val_det_apply] at h
      simpa using h
    refine ⟨hdet, ?_⟩
    obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp x.2
    have hbar : ⇑(fieldDataFour hK).bar = fun y : K => y ^ 2 :=
      funext (fieldDataFour_bar hK)
    rw [hbar, ← ht]
    exact diagGL_map_transpose_mul_eq_one hK t
  · intro hx
    have hdet := (mem_SU_iff (fieldDataFour hK)).mp hx |>.1
    apply Units.ext
    rw [Units.val_one, diagTorusDet, MonoidHom.comp_apply,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet

theorem card_torSU (hK : Nat.card K = 4) : Nat.card (torSU K) = 3 ^ 5 := by
  classical
  have hdt : Nat.card (TauCeti.diagonalTorus K 6) = 3 ^ 6 := by
    rw [TauCeti.natCard_diagonalTorus, hK]
  have hu : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  have hker := Subgroup.card_ker_mul_card_of_surjective (diagTorusDet_surjective (K := K))
  rw [hdt, hu] at hker
  have hker3 : Nat.card (diagTorusDet K).ker = 3 ^ 5 := by
    have h1 : Nat.card (diagTorusDet K).ker * 3 = 729 := by
      rw [show (729 : ℕ) = 3 ^ 6 by norm_num]
      exact hker
    have h2 : Nat.card (diagTorusDet K).ker = 243 := by omega
    rw [h2]
    norm_num
  have hSUker :
      Nat.card ((LargeEvenSUGroup (Fin 6) K (2 ^ 1)).subgroupOf
        (TauCeti.diagonalTorus K 6)) = 3 ^ 5 := by
    rw [← diagTorusDet_ker hK, hker3]
  have hinf : Nat.card ↥((TauCeti.diagonalTorus K 6) ⊓
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 3 ^ 5 := by
    have h := Subgroup.card_subtype (TauCeti.diagonalTorus K 6)
      ((LargeEvenSUGroup (Fin 6) K (2 ^ 1)).subgroupOf (TauCeti.diagonalTorus K 6))
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at h
    rw [h]
    exact hSUker
  have h := Subgroup.card_subtype (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (torSU K)
  rw [show torSU K = (TauCeti.diagonalTorus K 6).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) from rfl] at h
  rw [Subgroup.subgroupOf_map_subtype] at h
  change Nat.card ↥((TauCeti.diagonalTorus K 6).subgroupOf
    (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 3 ^ 5
  rw [← h]
  exact hinf

theorem card_torProj_ker (hK : Nat.card K = 4) :
    Nat.card ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).domRestrict
      (torSU K)).ker = 3 := by
  classical
  have hker_eq : ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).domRestrict
      (torSU K)).ker =
      ((LargeEvenScalars (Fin 6) K).subgroupOf
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).subgroupOf (torSU K) := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  rw [hker_eq]
  have hcard := Subgroup.card_subtype (torSU K)
    (((LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).subgroupOf (torSU K))
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (scalars_subgroupOf_le_torSU hK)] at hcard
  rw [← hcard, card_scalars_subgroupOf_SU hK]

section Centralizer

variable [Finite K] {ω : K}

theorem trace_diagTwoGL (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) :
    (((diagTwoGL (ω := ω) hω hij : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace = 1 := by
  rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  exact trace_diagTwo hK hω hij

section AutHelpers

theorem one_le_six : (1 : ℕ) ≤ 6 := by norm_num

theorem three_le_six : (3 : ℕ) ≤ 6 := by norm_num

theorem six_not_exception : ¬ ((6 : ℕ) = 3 ∧ (2 : ℕ) ^ 1 = 2) := by norm_num

variable [Finite K]

theorem trace_map_diagTwo (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) (φ : K ≃+* K) :
    (((diagTwo (ω := ω) i j).map φ)).trace = 1 := by
  rw [diagTwo, Matrix.diagonal_map (map_zero φ), Matrix.trace_diagonal]
  rw [← map_sum φ (fun k => diagVec ω i j k) Finset.univ]
  rw [diagVec_sum hK hω hij, map_one]

theorem conj_eq_diagTwo_of_fixes (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {A : ↥(uU (fieldDataFour hK) 6)} {φ : K ≃+* K} {i j : Fin 6} (hij : i ≠ j)
    (hfix : ((uConjAut (fieldDataFour hK) one_le_six A) *
      (uFieldAut (fieldDataFour hK) one_le_six φ))
      (CFSG.ComponentClassification.Burgoyne.Proj.projH
        (CFSG.Open.StatedSU 6 (2 ^ 1) K) (diagTwoSU (ω := ω) hω hij)) =
      CFSG.ComponentClassification.Burgoyne.Proj.projH
        (CFSG.Open.StatedSU 6 (2 ^ 1) K) (diagTwoSU (ω := ω) hω hij)) :
    (A : GL (Fin 6) K) * (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ
      (diagTwoGL (ω := ω) hω hij)) * (A : GL (Fin 6) K)⁻¹ =
      diagTwoGL (ω := ω) hω hij := by
  classical
  let h := fieldDataFour hK
  have hn : 1 ≤ (6 : ℕ) := by norm_num
  let d : ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K) := diagTwoSU (ω := ω) hω hij
  let L : ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K) := uLift h A φ d
  have hdGL : (d : GL (Fin 6) K) = diagTwoGL (ω := ω) hω hij :=
    coe_diagTwoSU hω hij
  have hfix' : CFSG.ComponentClassification.Burgoyne.Proj.projH
      (CFSG.Open.StatedSU 6 (2 ^ 1) K) L =
      CFSG.ComponentClassification.Burgoyne.Proj.projH
        (CFSG.Open.StatedSU 6 (2 ^ 1) K) d := by
    rw [show L = uLift h A φ d from rfl, ← uLift_proj h hn A φ d]
    exact hfix
  have hmem : L⁻¹ * d ∈ (CFSG.Open.StatedScalars (Fin 6) K).subgroupOf
      (CFSG.Open.StatedSU 6 (2 ^ 1) K) :=
    (CFSG.ComponentClassification.Burgoyne.Proj.projH_eq_projH_iff
      (H := CFSG.Open.StatedSU 6 (2 ^ 1) K)).mp hfix'
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcGL : (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) =
      (L : GL (Fin 6) K)⁻¹ * (d : GL (Fin 6) K) := by
    rw [hc]
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  have hLcGL : (L : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c =
      (d : GL (Fin 6) K) := by
    calc (L : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c =
        (L : GL (Fin 6) K) * ((L : GL (Fin 6) K)⁻¹ * (d : GL (Fin 6) K)) := by rw [hcGL]
      _ = (d : GL (Fin 6) K) := by group
  have hLgl : (L : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ *
      (d : GL (Fin 6) K) := by
    have h2 : (L : GL (Fin 6) K) =
        (d : GL (Fin 6) K) * (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by
      calc (L : GL (Fin 6) K) = (L : GL (Fin 6) K) *
            Matrix.GeneralLinearGroup.scalar (Fin 6) c *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by group
        _ = (d : GL (Fin 6) K) * (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by
            rw [hLcGL]
    rw [h2, ← map_inv]
    exact (Matrix.GeneralLinearGroup.scalar_commute c⁻¹ (d : GL (Fin 6) K)).symm
  have hdmat : ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagTwo (ω := ω) i j := by
    rw [hdGL, diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo]
  have htraceL : (((L : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace = 1 := by
    have hLmat : ((L : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map φ *
            ((((A : GL (Fin 6) K)⁻¹) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      dsimp [L]
      rw [coe_uLift]
    rw [hLmat, Matrix.trace_units_conj]
    rw [hdmat]
    exact trace_map_diagTwo hK hω hij φ
  have htrace_scalar : (((Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ *
      (d : GL (Fin 6) K) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace =
      (c⁻¹ : K) * (((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul, Units.val_inv_eq_inv_val]
  have htrace_d : (((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace = 1 := by
    rw [hdGL]
    exact trace_diagTwoGL hK hω hij
  have hcinv : (c⁻¹ : K) = 1 := by
    have hcalc : (c⁻¹ : K) * (((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace =
        (((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace := by
      rw [← htrace_scalar, ← hLgl, htraceL, htrace_d]
    rw [htrace_d, mul_one] at hcalc
    exact hcalc
  have hcunit : c⁻¹ = 1 := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact hcinv)
  have hLd : L = d := by
    apply Subtype.ext
    rw [hLgl, hcunit, map_one, one_mul]
  have hLmat2 : (((L : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    simpa using congrArg (fun x : ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hLd
  have hmat : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map φ *
        ((((A : GL (Fin 6) K)⁻¹) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    dsimp [L] at hLmat2
    rw [coe_uLift] at hLmat2
    exact hLmat2
  have hfinal : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (d : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) *
        (((A : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
    exact hmat
  rw [hdGL] at hfinal
  apply Units.ext
  change ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (diagTwoGL (ω := ω) hω hij) :
        Matrix (Fin 6) (Fin 6) K) *
        (((A : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((diagTwoGL (ω := ω) hω hij : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  exact hfinal

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem diagTwo_map_swaps (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) {φ : K ≃+* K} (hφ : φ ω = ω ^ 2) :
    (diagTwo (ω := ω) i j).map φ = diagTwo (ω := ω) j i := by
  unfold diagTwo
  rw [Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    rw [diagVec_self hij, diagVec_other hij.symm, hφ]
  · by_cases hkj : k = j
    · subst k
      rw [diagVec_other hij, diagVec_self hij.symm, map_pow, hφ]
      calc (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
        _ = 1 * ω := by rw [omega_cube hω]
        _ = ω := one_mul ω
    · rw [diagVec_of_ne hki hkj, diagVec_of_ne hkj hki, map_one]

theorem diagTwo_map_fixes (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) {φ : K ≃+* K} (hφ : φ ω = ω) :
    (diagTwo (ω := ω) i j).map φ = diagTwo (ω := ω) i j := by
  unfold diagTwo
  rw [Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    rw [diagVec_self hij, hφ]
  · by_cases hkj : k = j
    · subst k
      rw [diagVec_other hij, map_pow, hφ]
    · rw [diagVec_of_ne hki hkj, map_one]

theorem glAut_diagTwo_of_swaps (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) {φ : K ≃+* K} (hφ : φ ω = ω ^ 2) :
    ((glAut φ (diagTwoGL (ω := ω) hω hij) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) j i := by
  rw [coe_glAut, diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  exact diagTwo_map_swaps hK hω hij hφ

theorem glAut_diagTwo_of_fixes (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) {φ : K ≃+* K} (hφ : φ ω = ω) :
    ((glAut φ (diagTwoGL (ω := ω) hω hij) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) i j := by
  rw [coe_glAut, diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  exact diagTwo_map_fixes hK hω hij hφ

theorem isDiag_of_commute_diagTwo (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {M : Matrix (Fin 6) (Fin 6) K}
    (hcomm : ∀ i j (hij : i ≠ j), M * diagTwo (ω := ω) i j =
      diagTwo (ω := ω) i j * M) : M.IsDiag := by
  intro i j hij
  have h := congrArg (fun N : Matrix (Fin 6) (Fin 6) K => N i j) (hcomm i j hij)
  unfold diagTwo at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, diagVec_self hij, diagVec_other hij] at h
  have hzero : M i j * (ω ^ 2 - ω) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact h0
  · exact absurd h0 (sub_ne_zero.mpr (omega_sq_ne_omega hK hω))

theorem eq_zero_of_mul_diagTwo_swaps (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {M : Matrix (Fin 6) (Fin 6) K}
    (h01 : M * diagTwo (ω := ω) 1 0 = diagTwo (ω := ω) 0 1 * M)
    (h02 : M * diagTwo (ω := ω) 2 0 = diagTwo (ω := ω) 0 2 * M) :
    ∀ l, M 0 l = 0 := by
  have h01ne : (0 : Fin 6) ≠ 1 := by norm_num
  have h02ne : (0 : Fin 6) ≠ 2 := by norm_num
  have h12ne : (1 : Fin 6) ≠ 2 := by norm_num
  intro l
  by_cases hl0 : l = 0
  · subst l
    have h := congrArg (fun N : Matrix (Fin 6) (Fin 6) K => N 0 0) h01
    unfold diagTwo at h
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, diagVec_other h01ne.symm,
      diagVec_self h01ne] at h
    have hzero : M 0 0 * (ω ^ 2 - ω) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact h0
    · exact absurd h0 (sub_ne_zero.mpr (omega_sq_ne_omega hK hω))
  · by_cases hl1 : l = 1
    · subst l
      have h := congrArg (fun N : Matrix (Fin 6) (Fin 6) K => N 0 1) h02
      unfold diagTwo at h
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
        diagVec_of_ne h12ne (by norm_num : (1 : Fin 6) ≠ 0),
        diagVec_self h02ne] at h
      have hzero : M 0 1 * (1 - ω) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact h0
      · exact absurd h0 (sub_ne_zero.mpr (omega_ne_one hK hω).symm)
    · have h := congrArg (fun N : Matrix (Fin 6) (Fin 6) K => N 0 l) h01
      unfold diagTwo at h
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, diagVec_of_ne hl1 hl0,
        diagVec_self h01ne] at h
      have hzero : M 0 l * (1 - ω) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact h0
      · exact absurd h0 (sub_ne_zero.mpr (omega_ne_one hK hω).symm)
end AutHelpers
end Centralizer
end Card

theorem card_torU [Finite K] (hK : Nat.card K = 4) : Nat.card (torU K) = 3 ^ 4 := by
  classical
  have hrange : ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).domRestrict
      (torSU K)).range = torU K := by
    rw [MonoidHom.domRestrict_range]
    rfl
  have hcard := Subgroup.card_ker_mul_card_range
    ((LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))).domRestrict (torSU K))
  rw [card_torProj_ker hK, hrange, card_torSU hK] at hcard
  have h1 : 3 * Nat.card (torU K) = 3 * 3 ^ 4 := by
    simpa [show (3 : ℕ) ^ 5 = 3 * 3 ^ 4 by norm_num] using hcard
  have h2 : 3 * Nat.card (torU K) = 3 * 81 := by
    norm_num at h1 ⊢
    exact h1
  have h3 : Nat.card (torU K) = 81 := by omega
  rw [h3]
  norm_num

theorem threeA_mem_torU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : threeA hω ∈ torU K := by
  rw [threeA, torU]
  exact Subgroup.mem_map.mpr ⟨threeASU hω, by
    rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
    show (((threeASU hω : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
    rw [coe_threeASU]
    exact Matrix.isDiag_diagonal _, rfl⟩

theorem centralizer_torU [Finite K] (hK : Nat.card K = 4) :
    Subgroup.centralizer (torU K : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) =
      torU K := by
  classical
  let π : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) g
    have hAdiag : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
      apply isDiag_of_conj_torusSU_eq_smul hK
      intro d hd
      obtain ⟨v, hv3, hvprod, hdv⟩ := mem_torusSU_iff.mp hd
      have hSU : d ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
        rw [← hdv, mem_SU_iff (fieldDataFour hK)]
        constructor
        · rw [det_diagU]
          simpa using congrArg (fun u : Kˣ => (u : K)) hvprod
        · have hbar : ⇑(fieldDataFour hK).bar = fun y : K => y ^ 2 :=
            funext (fieldDataFour_bar hK)
          rw [hbar, diagU_val]
          exact diagonal_map_transpose_mul_eq_one (fun k => (v k : K))
            (fun k => congrArg (fun u : Kˣ => (u : K)) (hv3 k))
      let dSU : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := ⟨d, hSU⟩
      have hdSU : (dSU : GL (Fin 6) K) = diagU v := hdv.symm
      have hd_tor : π dSU ∈ torU K := by
        refine Subgroup.mem_map.mpr ⟨dSU, ?_, rfl⟩
        rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
        show ((dSU : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
        rw [hdSU]
        exact isDiag_diagU v
      have hcomm : π dSU * π A = π A * π dSU :=
        (Subgroup.mem_centralizer_iff.mp hg) (π dSU) hd_tor
      let B : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := A * dSU * A⁻¹
      have hB : π B = π dSU := by
        change π (A * dSU * A⁻¹) = π dSU
        rw [map_mul, map_mul, map_inv]
        calc π A * π dSU * (π A)⁻¹ = (π dSU * π A) * (π A)⁻¹ := by rw [← hcomm]
          _ = π dSU := by group
      have hmem : B⁻¹ * dSU ∈
          (LargeEvenScalars (Fin 6) K).subgroupOf
            (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
        (CFSG.ComponentClassification.Burgoyne.Proj.projH_eq_projH_iff
          (H := LargeEvenSUGroup (Fin 6) K (2 ^ 1))).mp hB
      rw [Subgroup.mem_subgroupOf] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hcGL : (Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) =
          (B : GL (Fin 6) K)⁻¹ * (dSU : GL (Fin 6) K) := by
        rw [hc]
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      have hBcGL : (B : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c =
          (dSU : GL (Fin 6) K) := by
        calc (B : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c =
            (B : GL (Fin 6) K) * ((B : GL (Fin 6) K)⁻¹ * (dSU : GL (Fin 6) K)) := by
              rw [hcGL]
          _ = (dSU : GL (Fin 6) K) := by group
      have hBgl : (B : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c⁻¹ *
          (dSU : GL (Fin 6) K) := by
        have h2 : (B : GL (Fin 6) K) =
            (dSU : GL (Fin 6) K) * (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by
          calc (B : GL (Fin 6) K) = (B : GL (Fin 6) K) *
                Matrix.GeneralLinearGroup.scalar (Fin 6) c *
                (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by group
            _ = (dSU : GL (Fin 6) K) *
                (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by rw [hBcGL]
        rw [h2, ← map_inv]
        exact (Matrix.GeneralLinearGroup.scalar_commute c⁻¹ (dSU : GL (Fin 6) K)).symm
      refine ⟨c⁻¹, ?_⟩
      have hBmat : ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          (c⁻¹ : K) • ((dSU : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
        have h := congrArg (fun g : GL (Fin 6) K =>
          ((g : Matrix (Fin 6) (Fin 6) K))) hBgl
        rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val] at h
        exact h
      rw [← hdv]
      simpa [B, hdSU] using hBmat
    have hAtor : A ∈ torSU K := by
      rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
      show ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
      exact hAdiag
    exact Subgroup.mem_map.mpr ⟨A, hAtor, rfl⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨A, hAtor, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨B, hBtor, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨ta, hta⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hAtor
    obtain ⟨tb, htb⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hBtor
    have hta' : (A : GL (Fin 6) K) = TauCeti.diagGL ta := hta.symm
    have htb' : (B : GL (Fin 6) K) = TauCeti.diagGL tb := htb.symm
    have hcommSU : A * B = B * A := by
      apply Subtype.ext
      show (A : GL (Fin 6) K) * (B : GL (Fin 6) K) = (B : GL (Fin 6) K) * (A : GL (Fin 6) K)
      rw [hta', htb', ← map_mul, ← map_mul, mul_comm]
    rw [← map_mul, ← map_mul]
    congr 1
    exact hcommSU.symm

theorem pow_three_eq_one_of_forall_fix_torU [Finite K] (hK : Nat.card K = 4)
    (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
    (hα : ∀ u ∈ torU K, α u = u) : α ^ 3 = 1 := by
  classical
  let α' : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K)) := α
  have hα' : ∀ u ∈ torU K, α' u = u := hα
  let h := fieldDataFour hK
  obtain ⟨A, φ, hAφ⟩ := exists_uConjAut_mul_uFieldAut h three_le_six six_not_exception α'
  obtain ⟨ω, hω⟩ := exists_root_omega hK
  have hfix_d : ∀ i j (hij : i ≠ j),
      ((uConjAut h one_le_six A) * (uFieldAut h one_le_six φ))
        (CFSG.ComponentClassification.Burgoyne.Proj.projH
          (CFSG.Open.StatedSU 6 (2 ^ 1) K) (diagTwoSU (ω := ω) hω hij)) =
      CFSG.ComponentClassification.Burgoyne.Proj.projH
        (CFSG.Open.StatedSU 6 (2 ^ 1) K) (diagTwoSU (ω := ω) hω hij) := by
    intro i j hij
    have hd : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        (diagTwoSU (ω := ω) hω hij) ∈ torU K :=
      Subgroup.mem_map.mpr ⟨diagTwoSU (ω := ω) hω hij, diagTwoSU_mem_torSU hω hij, rfl⟩
    have h := hα' _ hd
    rw [hAφ] at h
    exact h
  have hconj : ∀ i j (hij : i ≠ j), (A : GL (Fin 6) K) *
      (glAut φ (diagTwoGL (ω := ω) hω hij)) * (A : GL (Fin 6) K)⁻¹ =
      diagTwoGL (ω := ω) hω hij := by
    intro i j hij
    exact conj_eq_diagTwo_of_fixes hK hω hij (hfix_d i j hij)
  rcases ringEquiv_fixes_one_or_swaps hK hω (φ := φ) with hφ | hφ
  · have hφid : φ = RingEquiv.refl K := ringEquiv_fixes_all hK hω hφ
    have hcomm : ∀ i j (hij : i ≠ j),
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * diagTwo (ω := ω) i j =
          diagTwo (ω := ω) i j * ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      intro i j hij
      have h := hconj i j hij
      have hX : ((glAut φ (diagTwoGL (ω := ω) hω hij) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) i j :=
        glAut_diagTwo_of_fixes hK hω hij hφ
      have hD : ((diagTwoGL (ω := ω) hω hij : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) i j := by
        rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo]
      have hAcomm : (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω hij) =
          diagTwoGL (ω := ω) hω hij * (A : GL (Fin 6) K) := by
        calc (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω hij) =
            ((A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω hij) *
              (A : GL (Fin 6) K)⁻¹) * (A : GL (Fin 6) K) := by group
          _ = diagTwoGL (ω := ω) hω hij * (A : GL (Fin 6) K) := by rw [h]
      have hmat := congrArg (fun g : GL (Fin 6) K =>
        ((g : Matrix (Fin 6) (Fin 6) K))) hAcomm
      simp only [Units.val_mul] at hmat
      rw [hX, hD] at hmat
      exact hmat
    have hAdiag : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag :=
      isDiag_of_commute_diagTwo hK hω hcomm
    have hbar : h.bar = fun x : K => x ^ 2 := funext (fieldDataFour_bar hK)
    have huni : (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ *
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := (mem_uU h).mp A.2
    rw [hbar] at huni
    have hAeq : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.diagonal (fun i => ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) :=
      hAdiag.diagonal_diag.symm
    rw [hAeq] at huni
    rw [Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one] at huni
    have hcube : ∀ i, (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) ^ 3 = 1 := by
      intro i
      have h := congrFun huni i
      simp only [Pi.one_apply] at h
      rw [show (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) ^ 2 *
        (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) =
        (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i) ^ 3 by ring] at h
      exact h
    have hmat3 : (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ^ 3 = 1 := by
      rw [hAeq, Matrix.diagonal_pow, Matrix.diagonal_eq_one]
      funext i
      exact hcube i
    have hA3 : A ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      apply Units.ext
      simpa using hmat3
    have hf_one : uFieldAut h one_le_six φ = 1 := by
      rw [hφid]
      change (uFieldAut h one_le_six) (1 : K ≃+* K) = 1
      exact map_one _
    have hαeq : α' = uConjAut h one_le_six A := by
      rw [hAφ, hf_one, mul_one]
    have hα3 : α' ^ 3 = 1 := by
      rw [hαeq, ← map_pow, hA3, map_one]
    change α' ^ 3 = 1
    exact hα3
  · exfalso
    have h01ne : (0 : Fin 6) ≠ 1 := by norm_num
    have h02ne : (0 : Fin 6) ≠ 2 := by norm_num
    have hcomm01 : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagTwo (ω := ω) 1 0 = diagTwo (ω := ω) 0 1 *
          ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      have h := hconj 0 1 h01ne
      have hX : ((glAut φ (diagTwoGL (ω := ω) hω h01ne) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) 1 0 :=
        glAut_diagTwo_of_swaps hK hω h01ne hφ
      have hD : ((diagTwoGL (ω := ω) hω h01ne : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) 0 1 := by
        rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo]
      have hAcomm : (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h01ne) =
          diagTwoGL (ω := ω) hω h01ne * (A : GL (Fin 6) K) := by
        calc (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h01ne) =
            ((A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h01ne) *
              (A : GL (Fin 6) K)⁻¹) * (A : GL (Fin 6) K) := by group
          _ = diagTwoGL (ω := ω) hω h01ne * (A : GL (Fin 6) K) := by rw [h]
      have hmat := congrArg (fun g : GL (Fin 6) K =>
        ((g : Matrix (Fin 6) (Fin 6) K))) hAcomm
      simp only [Units.val_mul] at hmat
      rwa [hX, hD] at hmat
    have hcomm02 : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagTwo (ω := ω) 2 0 = diagTwo (ω := ω) 0 2 *
          ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      have h := hconj 0 2 h02ne
      have hX : ((glAut φ (diagTwoGL (ω := ω) hω h02ne) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) 2 0 :=
        glAut_diagTwo_of_swaps hK hω h02ne hφ
      have hD : ((diagTwoGL (ω := ω) hω h02ne : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) = diagTwo (ω := ω) 0 2 := by
        rw [diagTwoGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagTwo]
      have hAcomm : (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h02ne) =
          diagTwoGL (ω := ω) hω h02ne * (A : GL (Fin 6) K) := by
        calc (A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h02ne) =
            ((A : GL (Fin 6) K) * glAut φ (diagTwoGL (ω := ω) hω h02ne) *
              (A : GL (Fin 6) K)⁻¹) * (A : GL (Fin 6) K) := by group
          _ = diagTwoGL (ω := ω) hω h02ne * (A : GL (Fin 6) K) := by rw [h]
      have hmat := congrArg (fun g : GL (Fin 6) K =>
        ((g : Matrix (Fin 6) (Fin 6) K))) hAcomm
      simp only [Units.val_mul] at hmat
      rwa [hX, hD] at hmat
    have hrow := eq_zero_of_mul_diagTwo_swaps hK hω hcomm01 hcomm02
    have hmulGL := Units.mul_inv (A : GL (Fin 6) K)
    have hmul : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((A : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      simpa using congrArg (fun g : GL (Fin 6) K =>
        ((g : Matrix (Fin 6) (Fin 6) K))) hmulGL
    have hentry := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M 0 0) hmul
    simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero] at hentry
    simp at hentry

@[expose] noncomputable def SUu (hK : Nat.card K = 4) :
    Subgroup ↥(uU (fieldDataFour hK) 6) :=
  (LargeEvenSUGroup (Fin 6) K (2 ^ 1)).comap (uU (fieldDataFour hK) 6).subtype

theorem mem_SUu (hK : Nat.card K = 4) {A : ↥(uU (fieldDataFour hK) 6)} :
    A ∈ SUu hK ↔ (A : GL (Fin 6) K) ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  rw [SUu, Subgroup.mem_comap]
  rfl

theorem inn_eq_map_SUu [Finite K] (hK : Nat.card K = 4) :
    (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K) →*
      MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K))).range =
    (SUu hK).map (uConjAut (fieldDataFour hK) one_le_six) := by
  ext α
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
      ((CFSG.Open.StatedScalars (Fin 6) K).subgroupOf
        (CFSG.Open.StatedSU 6 (2 ^ 1) K)) y
    let A : ↥(uU (fieldDataFour hK) 6) :=
      ⟨(s : GL (Fin 6) K), statedSU_le_uU (fieldDataFour hK) s.2⟩
    refine ⟨A, ?_, ?_⟩
    · change (A : GL (Fin 6) K) ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1)
      exact s.2
    · refine MulEquiv.ext fun z => ?_
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective
        ((CFSG.Open.StatedScalars (Fin 6) K).subgroupOf
          (CFSG.Open.StatedSU 6 (2 ^ 1) K)) z
      change (uConjAut (fieldDataFour hK) one_le_six A)
          (CFSG.ComponentClassification.Burgoyne.Proj.projH
            (CFSG.Open.StatedSU 6 (2 ^ 1) K) t) =
        MulAut.conj (CFSG.ComponentClassification.Burgoyne.Proj.projH
          (CFSG.Open.StatedSU 6 (2 ^ 1) K) s)
          (CFSG.ComponentClassification.Burgoyne.Proj.projH
            (CFSG.Open.StatedSU 6 (2 ^ 1) K) t)
      rw [MulAut.conj_apply, uConjAut_proj (fieldDataFour hK) one_le_six A t]
      rw [← map_inv, ← map_mul]
      rfl
  · rintro ⟨A, hA, rfl⟩
    have hASU : (A : GL (Fin 6) K) ∈ CFSG.Open.StatedSU 6 (2 ^ 1) K :=
      (mem_SUu hK).mp hA
    refine ⟨QuotientGroup.mk' _ ⟨(A : GL (Fin 6) K), hASU⟩, ?_⟩
    · refine MulEquiv.ext fun z => ?_
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective
        ((CFSG.Open.StatedScalars (Fin 6) K).subgroupOf
          (CFSG.Open.StatedSU 6 (2 ^ 1) K)) z
      change MulAut.conj (CFSG.ComponentClassification.Burgoyne.Proj.projH
          (CFSG.Open.StatedSU 6 (2 ^ 1) K)
          (⟨(A : GL (Fin 6) K), hASU⟩ : ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K)))
          (CFSG.ComponentClassification.Burgoyne.Proj.projH
            (CFSG.Open.StatedSU 6 (2 ^ 1) K) t) =
        (uConjAut (fieldDataFour hK) one_le_six A)
          (CFSG.ComponentClassification.Burgoyne.Proj.projH
            (CFSG.Open.StatedSU 6 (2 ^ 1) K) t)
      rw [MulAut.conj_apply, uConjAut_proj (fieldDataFour hK) one_le_six A t]
      rw [← map_inv, ← map_mul]
      rfl

theorem index_range_conj_dvd_six [Finite K] (hK : Nat.card K = 4) :
    (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range.index ∣ 6 := by
  change (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K) →*
    MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K))).range.index ∣ 6
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  let e : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K) ≃* CFSG.Open.timmesfeldPSU 6 :=
    (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1)).trans
      (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 6).symm
  rw [Subgroup.index_eq_card]
  change Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
    (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K))) ∣ 6
  rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
    CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU_six]

end CFSG.StandardType.USixTwo

end
