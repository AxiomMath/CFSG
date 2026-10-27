module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.Quasithin.SteinbergBSCubicPair

public section

namespace CFSG.Quasithin.SteinbergBS

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.ComponentClassification CFSG.ABGLocalTools
open scoped MatrixGroups Pointwise

section Coordinates

variable {F : Type} [Field F]

theorem up3_mem_unitriangular (x y z : F) : up3 x y z ∈ LinearFlag.unitriangular 3 F := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [up3_coe, upMat]
  · fin_cases i <;> simp [up3_coe, upMat]

theorem up3_mul_self [CharP F 2] (x y z : F) : up3 x y z * up3 x y z = up3 0 (z * x) 0 := by
  rw [up3_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    zero_add]

theorem up3_comm_iff (x y z X Y Z : F) :
    up3 x y z * up3 X Y Z = up3 X Y Z * up3 x y z ↔ z * X = Z * x := by
  rw [up3_mul, up3_mul]
  constructor
  · intro h
    obtain ⟨-, h2, -⟩ := up3_inj h
    linear_combination h2
  · intro h
    rw [add_comm x X, add_comm z Z, add_comm y Y, h]

@[expose] def uniRadOne (F : Type) [Field F] [CharP F 2] : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F => up3 p.1 p.2 0
  one_mem' := ⟨(0, 0), up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨x, y⟩, rfl⟩ ⟨⟨X, Y⟩, rfl⟩
    exact ⟨(x + X, y + Y), by rw [up3_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨(x, y), by rw [up3_inv]; simp⟩

@[expose] def uniRadTwo (F : Type) [Field F] [CharP F 2] : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F => up3 0 p.1 p.2
  one_mem' := ⟨(0, 0), up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨y, z⟩, rfl⟩ ⟨⟨Y, Z⟩, rfl⟩
    exact ⟨(y + Y, z + Z), by rw [up3_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨⟨y, z⟩, rfl⟩
    exact ⟨(y, z), by rw [up3_inv]; simp⟩

@[expose] def uniCenter (F : Type) [Field F] : Subgroup SL(3, F) where
  carrier := Set.range fun y : F => up3 0 y 0
  one_mem' := ⟨0, up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨Y, rfl⟩
    exact ⟨y + Y, by rw [up3_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨y, rfl⟩
    refine ⟨-y, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [up3_mul]
    simp [up3_zero]

theorem mem_uniRadOne [CharP F 2] {g : SL(3, F)} : g ∈ uniRadOne F ↔ ∃ x y, g = up3 x y 0 :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp.symm⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h.symm⟩⟩

theorem mem_uniRadTwo [CharP F 2] {g : SL(3, F)} : g ∈ uniRadTwo F ↔ ∃ y z, g = up3 0 y z :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp.symm⟩, fun ⟨y, z, h⟩ => ⟨(y, z), h.symm⟩⟩

theorem mem_uniCenter {g : SL(3, F)} : g ∈ uniCenter F ↔ ∃ y, g = up3 0 y 0 :=
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩

theorem proj_injOn_unitriangular {u v : SL(3, F)} (hu : u ∈ LinearFlag.unitriangular 3 F)
    (hv : v ∈ LinearFlag.unitriangular 3 F) (h : proj 3 F u = proj 3 F v) : u = v := by
  have h3 : u⁻¹ * v ∈ LinearFlag.unitriangular 3 F ⊓ scalars 3 F :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hv, proj_eq_proj_iff.1 h⟩
  rw [unitriangular_inf_scalars, mem_bot] at h3
  exact inv_mul_eq_one.1 h3

theorem exists_up3_of_mem_projUnitriangular {g : projectiveSL 3 F}
    (hg : g ∈ projUnitriangular 3 F) : ∃ x y z : F, g = proj 3 F (up3 x y z) := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_unitriangular hu
  exact ⟨x, y, z, rfl⟩

theorem proj_up3_inj {x y z X Y Z : F} (h : proj 3 F (up3 x y z) = proj 3 F (up3 X Y Z)) :
    x = X ∧ y = Y ∧ z = Z :=
  up3_inj (proj_injOn_unitriangular (up3_mem_unitriangular x y z) (up3_mem_unitriangular X Y Z) h)

theorem le_projRad_of_elementary [CharP F 2] {E : Subgroup (projectiveSL 3 F)}
    (hEU : E ≤ projUnitriangular 3 F) (hE2 : ∀ g ∈ E, g * g = 1)
    (hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    E ≤ (uniRadOne F).map (proj 3 F) ∨ E ≤ (uniRadTwo F).map (proj 3 F) := by
  have hsq : ∀ x y z : F, proj 3 F (up3 x y z) ∈ E → z * x = 0 := by
    intro x y z hg
    have h1 := hE2 _ hg
    rw [← map_mul, up3_mul_self, ← map_one (proj 3 F), ← up3_zero] at h1
    exact (proj_up3_inj h1).2.1
  have hcomm : ∀ x y z X Y Z : F, proj 3 F (up3 x y z) ∈ E → proj 3 F (up3 X Y Z) ∈ E →
      z * X = Z * x := by
    intro x y z X Y Z hg hh
    have h1 := hEc _ hg _ hh
    rw [← map_mul, ← map_mul] at h1
    have h2 := proj_injOn_unitriangular (mul_mem (up3_mem_unitriangular x y z)
      (up3_mem_unitriangular X Y Z)) (mul_mem (up3_mem_unitriangular X Y Z)
      (up3_mem_unitriangular x y z)) h1
    exact (up3_comm_iff x y z X Y Z).1 h2
  by_cases hz : ∃ x y z : F, z ≠ 0 ∧ proj 3 F (up3 x y z) ∈ E
  ·
    obtain ⟨x₀, y₀, z₀, hz₀, hg₀⟩ := hz
    have hx₀ : x₀ = 0 := (mul_eq_zero.1 (hsq _ _ _ hg₀)).resolve_left hz₀
    right
    intro g hg
    obtain ⟨X, Y, Z, rfl⟩ := exists_up3_of_mem_projUnitriangular (hEU hg)
    have h1 := hcomm _ _ _ _ _ _ hg₀ hg
    rw [hx₀, mul_zero] at h1
    have hX : X = 0 := (mul_eq_zero.1 h1).resolve_left hz₀
    rw [hX]
    exact mem_map_of_mem _ (mem_uniRadTwo.2 ⟨Y, Z, rfl⟩)
  ·
    push Not at hz
    left
    intro g hg
    obtain ⟨X, Y, Z, rfl⟩ := exists_up3_of_mem_projUnitriangular (hEU hg)
    rw [show Z = 0 from by_contra fun hZ => hz X Y Z hZ hg]
    exact mem_map_of_mem _ (mem_uniRadOne.2 ⟨X, Y, rfl⟩)

theorem projRad_inf_eq [CharP F 2] :
    (uniRadOne F).map (proj 3 F) ⊓ (uniRadTwo F).map (proj 3 F) =
      (uniCenter F).map (proj 3 F) := by
  apply le_antisymm
  · rintro g ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    obtain ⟨x, y, rfl⟩ := mem_uniRadOne.1 hu
    obtain ⟨Y, Z, rfl⟩ := mem_uniRadTwo.1 hv
    obtain ⟨h1, -, -⟩ := proj_up3_inj hvu
    rw [← h1]
    exact mem_map_of_mem _ (mem_uniCenter.2 ⟨y, rfl⟩)
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, rfl⟩ := mem_uniCenter.1 hu
    exact ⟨mem_map_of_mem _ (mem_uniRadOne.2 ⟨0, y, rfl⟩),
      mem_map_of_mem _ (mem_uniRadTwo.2 ⟨y, 0, rfl⟩)⟩

theorem mem_projCenter_iff {g : projectiveSL 3 F} :
    g ∈ (uniCenter F).map (proj 3 F) ↔
      g ∈ projUnitriangular 3 F ∧ ∀ h ∈ projUnitriangular 3 F, g * h = h * g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, rfl⟩ := mem_uniCenter.1 hu
    refine ⟨mem_map_of_mem _ (up3_mem_unitriangular _ _ _), fun h hh => ?_⟩
    obtain ⟨X, Y, Z, rfl⟩ := exists_up3_of_mem_projUnitriangular hh
    rw [← map_mul, ← map_mul, (up3_comm_iff 0 y 0 X Y Z).2 (by ring)]
  · rintro ⟨hg, hc⟩
    obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    have hcomm : ∀ X Z : F, z * X = Z * x := fun X Z => by
      have h1 := hc _ (mem_map_of_mem _ (up3_mem_unitriangular X 0 Z))
      rw [← map_mul, ← map_mul] at h1
      exact (up3_comm_iff x y z X 0 Z).1 (proj_injOn_unitriangular
        (mul_mem (up3_mem_unitriangular x y z) (up3_mem_unitriangular X 0 Z))
        (mul_mem (up3_mem_unitriangular X 0 Z) (up3_mem_unitriangular x y z)) h1)
    have hz : z = 0 := by linear_combination hcomm 1 0
    have hx : x = 0 := by linear_combination -(hcomm 0 1)
    rw [hx, hz]
    exact mem_map_of_mem _ (mem_uniCenter.2 ⟨y, rfl⟩)

theorem exists_formula_of_not_mem_semilinear [Finite F] {r : MulAut (projectiveSL 3 F)}
    (hr : r ∉ semilinearAutGroup 3 F) :
    ∃ (D : GL (Fin 3) F) (σ : F ≃+* F), r = conjAut 3 F D * fieldAut 3 F σ * dualAut 3 F := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨D, σ, ε, hε, hrε⟩ := hgen r
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · refine absurd ?_ hr
    rw [hrε, pow_zero, mul_one]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup D))
      (fieldAut_mem_semilinearAutGroup σ)
  · exact ⟨D, σ, by rw [hrε, pow_one]⟩

@[expose] noncomputable def gammaZero (F : Type) [Field F] [CharP F 2] :
    MulAut (projectiveSL 3 F) :=
  conjAut 3 F (SpecialLinearGroup.toGL (wJ : SL(3, F))) * dualAut 3 F

theorem gammaZero_apply [CharP F 2] (x y z : F) :
    gammaZero F (proj 3 F (up3 x y z)) = proj 3 F (up3 z (y + z * x) x) := by
  rw [gammaZero, MulAut.mul_apply, dualAut_proj, conjAut_proj, up3_inv]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := rfl
  have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, F)))⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := by
    rw [← map_inv, wJ_inv]
    rfl
  rw [h1, h2]
  show wJMat * (upMat x (y + z * x) z)ᵀ * wJMat = upMat z (y + z * x) x
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [wJMat, upMat]

theorem slConjugation_mem_unitriangular {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) {g : SL(3, F)}
    (hg : g ∈ LinearFlag.unitriangular 3 F) :
    CatalogueBHigherLinearAction.slConjugation 3 F A g ∈ LinearFlag.unitriangular 3 F := by
  have hA' : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hA _ _ h
  have hAi : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hA'
  have hg' : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hg.1 _ _ h
  rw [mem_unitriangular, coe_slConjugation]
  refine ⟨fun i j hij => (hA'.mul hg').mul hAi hij, fun i => ?_⟩
  have h1 : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mul_apply_self_of_isUpperTriangular (hA'.mul hg') hAi,
    mul_apply_self_of_isUpperTriangular hA' hg', hg.2 i, mul_one,
    ← mul_apply_self_of_isUpperTriangular hA' hAi, h1, one_apply_eq]

theorem semilinear_apply_up3 {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) (σ : F ≃+* F)
    (x y z : F) :
    ∃ x' y' z' : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (up3 x y z)) =
      proj 3 F (up3 x' y' z') ∧ x' * (A : Matrix (Fin 3) (Fin 3) F) 2 2 =
        (A : Matrix (Fin 3) (Fin 3) F) 1 1 * σ x ∧
      z' * (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ z := by
  set M := SpecialLinearGroup.map σ.toRingHom (up3 x y z) with hM
  have hMc : (M : Matrix (Fin 3) (Fin 3) F) = upMat (σ x) (σ y) (σ z) := by
    rw [hM, SpecialLinearGroup.map_apply_coe, up3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upMat, RingHom.mapMatrix_apply]
  have hMu : M ∈ LinearFlag.unitriangular 3 F := by
    rw [mem_unitriangular, hMc]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [upMat]
    · fin_cases i <;> simp [upMat]
  set X := CatalogueBHigherLinearAction.slConjugation 3 F A M with hX
  obtain ⟨x', y', z', hX'⟩ :=
    exists_up3_of_mem_unitriangular (slConjugation_mem_unitriangular hA hMu)
  rw [← hX] at hX'
  refine ⟨x', y', z', ?_, ?_, ?_⟩
  · rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, ← hM, ← hX, hX']
  ·
    have hXA : (X : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by
      rw [hX, coe_slConjugation, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one]
    have h1 := congrFun (congrFun hXA 1) 2
    rw [hX', up3_coe, hMc] at h1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, upMat] at h1
    simp [hA 1 0 (by decide)] at h1
    linear_combination h1
  · have hXA : (X : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by
      rw [hX, coe_slConjugation, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one]
    have h1 := congrFun (congrFun hXA 0) 1
    rw [hX', up3_coe, hMc] at h1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, upMat] at h1
    simp [hA 2 1 (by decide)] at h1
    linear_combination h1

theorem upperTriangular_of_semilinear_normalizes {A : GL (Fin 3) F} {σ : F ≃+* F}
    (hU : (projUnitriangular 3 F).map (conjAut 3 F A * fieldAut 3 F σ).toMonoidHom =
      projUnitriangular 3 F) :
    ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hα : conjAut 3 F A * fieldAut 3 F σ ∈ semilinearAutGroup 3 F :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (conjAut 3 F B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : F ≃+* F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (fieldAut 3 F τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    fun τ W => htrans.2.2.2.2.2.2.2.1 τ W
  have hflag : ∀ d ≤ 3,
      (flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = flagSpace 3 F d := by
    intro d hd
    have h1 := CFSG.QuasithinUnique.Setup.X7Sec.semilinear_flag hα hU hd
    have hmap : (projStabilizer (flagSpace 3 F d)).map
        (conjAut 3 F A * fieldAut 3 F σ).toMonoidHom =
        projStabilizer ((flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
      rw [CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, h8,
        CFSG.QuasithinUnique.Setup.X7Sec.coordImage_flagSpace, h7]
    have hle : projUnitriangular 3 F ≤
        projStabilizer ((flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
      rw [← hmap, h1]
      exact CFSG.QuasithinUnique.Setup.X7Sec.projUnitriangular_le_projStabilizer_flag d
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant
      (CFSG.QuasithinUnique.Setup.X7Sec.invariant_of_projUnitriangular_le hle)
    have hdim := CFSG.QuasithinUnique.Setup.Family.finrank_map_mulVecLin_gl A (flagSpace 3 F d)
    rw [hW, finrank_flagSpace hm, finrank_flagSpace hd] at hdim
    rw [hW, hdim]
  intro i j hij
  have h1 := hflag ((j : ℕ) + 1) (by omega)
  have hv : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 ∈ flagSpace 3 F ((j : ℕ) + 1) := by
    rw [← h1]
    refine ⟨Pi.single j 1, mem_flagSpace.2 fun k hk => ?_, rfl⟩
    rw [Pi.single_eq_of_ne (fun h => by rw [h] at hk; omega)]
  have h2 := mem_flagSpace.1 hv i (by omega)
  rwa [mulVec_single_one, col_apply] at h2

theorem diag_ne_zero_of_upperTriangular {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) (i : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
  have h1 : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hU : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hA _ _ h
  rw [Matrix.det_of_isUpperTriangular hU] at h1
  exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)

theorem map_projUnitriangular_gammaZero [CharP F 2] :
    (projUnitriangular 3 F).map (gammaZero F).toMonoidHom = projUnitriangular 3 F := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    show gammaZero F _ ∈ _
    rw [gammaZero_apply]
    exact mem_map_of_mem _ (up3_mem_unitriangular _ _ _)
  · intro g hg
    obtain ⟨a, b, c, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    refine ⟨proj 3 F (up3 c (b + a * c) a), mem_map_of_mem _ (up3_mem_unitriangular _ _ _), ?_⟩
    show gammaZero F _ = _
    rw [gammaZero_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem map_inv_eq_of_map_eq {G : Type*} [Group G] {X : Subgroup G} {e : MulAut G}
    (h : X.map e.toMonoidHom = X) : X.map e⁻¹.toMonoidHom = X := by
  conv_lhs => rw [← h]
  rw [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, inv_mul_cancel]
  ext x
  simp

theorem exists_eq_semilinear_mul_gammaZero [Finite F] [CharP F 2]
    {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ semilinearAutGroup 3 F) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) ∧
        α = conjAut 3 F A * fieldAut 3 F σ * gammaZero F := by
  obtain ⟨A, σ, hα⟩ := exists_formula_of_not_mem_semilinear hαs
  have hAσ : conjAut 3 F A * fieldAut 3 F σ ∈ semilinearAutGroup 3 F :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  set β := α * (gammaZero F)⁻¹ with hβ
  have hβs : β ∈ semilinearAutGroup 3 F := by
    rw [hβ, hα, gammaZero, _root_.mul_inv_rev,
      show conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F * ((dualAut 3 F)⁻¹ *
        (conjAut 3 F (SpecialLinearGroup.toGL (wJ : SL(3, F))))⁻¹) =
        conjAut 3 F A * fieldAut 3 F σ * (conjAut 3 F (SpecialLinearGroup.toGL wJ))⁻¹ by group]
    exact mul_mem hAσ (inv_mem (linearAutGroup_le_semilinearAutGroup
      (conjAut_mem_linearAutGroup _)))
  have hβU : (projUnitriangular 3 F).map β.toMonoidHom = projUnitriangular 3 F := by
    rw [hβ, CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      map_inv_eq_of_map_eq map_projUnitriangular_gammaZero, hαU]
  obtain ⟨B, τ, hβeq⟩ := mem_semilinearAutGroup_iff.1 hβs
  rw [hβeq] at hβU
  refine ⟨B, τ, upperTriangular_of_semilinear_normalizes hβU, ?_⟩
  rw [← hβeq, hβ, inv_mul_cancel_right]

theorem map_uniRadOne_le_of_not_mem_semilinear [Finite F] [CharP F 2]
    {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ semilinearAutGroup 3 F) :
    ((uniRadOne F).map (proj 3 F)).map α.toMonoidHom ≤ (uniRadTwo F).map (proj 3 F) := by
  obtain ⟨B, τ, hB, hαβ⟩ := exists_eq_semilinear_mul_gammaZero hαU hαs
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨x, y, rfl⟩ := mem_uniRadOne.1 hu
  show α (proj 3 F (up3 x y 0)) ∈ _
  rw [hαβ, MulAut.mul_apply, gammaZero_apply]
  obtain ⟨x', y', z', he, hx', -⟩ := semilinear_apply_up3 hB τ 0 (y + 0 * x) x
  rw [he]
  have hx0 : x' = 0 := by
    rw [map_zero, mul_zero] at hx'
    exact (mul_eq_zero.1 hx').resolve_right (diag_ne_zero_of_upperTriangular hB 2)
  rw [hx0]
  exact mem_map_of_mem _ (mem_uniRadTwo.2 ⟨y', z', rfl⟩)

theorem map_uniRadTwo_le_of_not_mem_semilinear [Finite F] [CharP F 2]
    {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ semilinearAutGroup 3 F) :
    ((uniRadTwo F).map (proj 3 F)).map α.toMonoidHom ≤ (uniRadOne F).map (proj 3 F) := by
  obtain ⟨B, τ, hB, hαβ⟩ := exists_eq_semilinear_mul_gammaZero hαU hαs
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨y, z, rfl⟩ := mem_uniRadTwo.1 hu
  show α (proj 3 F (up3 0 y z)) ∈ _
  rw [hαβ, MulAut.mul_apply, gammaZero_apply]
  obtain ⟨x', y', z', he, -, hz'⟩ := semilinear_apply_up3 hB τ z (y + z * 0) 0
  rw [he]
  have hz0 : z' = 0 := by
    rw [map_zero, mul_zero] at hz'
    exact (mul_eq_zero.1 hz').resolve_right (diag_ne_zero_of_upperTriangular hB 1)
  rw [hz0]
  exact mem_map_of_mem _ (mem_uniRadOne.2 ⟨x', y', rfl⟩)

theorem exists_eq_conj_of_trivial_mod_center [Finite F] [CharP F 2]
    {e : MulAut (projectiveSL 3 F)}
    (heU : (projUnitriangular 3 F).map e.toMonoidHom = projUnitriangular 3 F)
    (htriv : ∀ u ∈ projUnitriangular 3 F, e u * u⁻¹ ∈ (uniCenter F).map (proj 3 F)) :
    ∃ v ∈ projUnitriangular 3 F, e = MulAut.conj v := by
  have hes : e ∈ semilinearAutGroup 3 F := by
    by_contra hes
    have h1 := map_uniRadOne_le_of_not_mem_semilinear heU hes
    set u := proj 3 F (up3 (1 : F) 0 0) with hu
    have hu1 : u ∈ (uniRadOne F).map (proj 3 F) := mem_map_of_mem _ (mem_uniRadOne.2 ⟨1, 0, rfl⟩)
    have h2 : e u ∈ (uniRadTwo F).map (proj 3 F) := h1 ⟨u, hu1, rfl⟩
    have h3 : e u * u⁻¹ ∈ (uniRadTwo F).map (proj 3 F) := by
      have h4 := htriv u (mem_map_of_mem _ (up3_mem_unitriangular _ _ _))
      rw [← projRad_inf_eq] at h4
      exact h4.2
    have h5 : u ∈ (uniRadTwo F).map (proj 3 F) := by
      have h6 := mul_mem (inv_mem h3) h2
      rwa [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h6
    obtain ⟨v, hv, hvu⟩ := h5
    obtain ⟨y, z, rfl⟩ := mem_uniRadTwo.1 hv
    have := (proj_up3_inj hvu).1
    exact zero_ne_one this
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hes
  have hA := upperTriangular_of_semilinear_normalizes heU
  have hdiag := diag_ne_zero_of_upperTriangular hA
  have hZ : ∀ a b c : F, proj 3 F (up3 a b c) ∈ (uniCenter F).map (proj 3 F) → a = 0 ∧ c = 0 := by
    rintro a b c ⟨w, hw, hwe⟩
    obtain ⟨t, rfl⟩ := mem_uniCenter.1 hw
    obtain ⟨h1, -, h3⟩ := proj_up3_inj hwe
    exact ⟨h1.symm, h3.symm⟩
  have hx : ∀ x : F, x * (A : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (A : Matrix (Fin 3) (Fin 3) F) 1 1 * σ x := by
    intro x
    obtain ⟨x', y', z', he, hx', hz'⟩ := semilinear_apply_up3 hA σ x 0 0
    have h1 := htriv _ (mem_map_of_mem _ (up3_mem_unitriangular x 0 0))
    rw [he, ← map_inv, ← map_mul, up3_inv, up3_mul] at h1
    have h2 := (hZ _ _ _ h1).1
    have hxx : x' = x := by
      have := congrArg (· + x) h2
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    calc x * (A : Matrix (Fin 3) (Fin 3) F) 2 2 = x' * (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
          rw [hxx]
      _ = _ := hx'
  have hz : ∀ z : F, z * (A : Matrix (Fin 3) (Fin 3) F) 1 1 =
      (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ z := by
    intro z
    obtain ⟨x', y', z', he, hx', hz'⟩ := semilinear_apply_up3 hA σ 0 0 z
    have h1 := htriv _ (mem_map_of_mem _ (up3_mem_unitriangular 0 0 z))
    rw [he, ← map_inv, ← map_mul, up3_inv, up3_mul] at h1
    have h2 := (hZ _ _ _ h1).2
    have hzz : z' = z := by
      have := congrArg (· + z) h2
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    calc z * (A : Matrix (Fin 3) (Fin 3) F) 1 1 = z' * (A : Matrix (Fin 3) (Fin 3) F) 1 1 := by
          rw [hzz]
      _ = _ := hz'
  have h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 1 1 := by
    have := hx 1
    rwa [one_mul, map_one, mul_one] at this
  have h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    have := hz 1
    rwa [one_mul, map_one, mul_one] at this
  have hσ : σ = 1 := by
    ext x
    have h1 := hx x
    rw [h21, mul_comm] at h1
    exact (mul_left_cancel₀ (hdiag 1) h1).symm
  set d : Fˣ := Units.mk0 ((A : Matrix (Fin 3) (Fin 3) F) 0 0) (hdiag 0) with hd
  set N : Matrix (Fin 3) (Fin 3) F := ((d⁻¹ : Fˣ) : F) • (A : Matrix (Fin 3) (Fin 3) F) with hN
  have hNdet : N.det = 1 := by
    have hU : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hA _ _ h
    rw [hN, Matrix.det_smul, Matrix.det_of_isUpperTriangular hU, Fin.prod_univ_three, h21, h10,
      Fintype.card_fin]
    have h0 := hdiag 0
    rw [hd, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  set Nsl : SL(3, F) := ⟨N, hNdet⟩ with hNsl
  have hNu : Nsl ∈ LinearFlag.unitriangular 3 F := by
    rw [mem_unitriangular]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · show N i j = 0
      rw [hN, Matrix.smul_apply, hA i j hij, smul_zero]
    · show N i i = 1
      rw [hN, Matrix.smul_apply, smul_eq_mul, hd, Units.val_inv_eq_inv_val, Units.val_mk0]
      have : (A : Matrix (Fin 3) (Fin 3) F) i i = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
        fin_cases i
        · rfl
        · exact h10
        · exact h21.trans h10
      rw [this]
      exact inv_mul_cancel₀ (hdiag 0)
  have hAeq : A = GeneralLinearGroup.scalar (Fin 3) d * SpecialLinearGroup.toGL Nsl := by
    ext i j
    show (A : Matrix (Fin 3) (Fin 3) F) i j =
      (Matrix.scalar (Fin 3) (d : F) * N) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, hN, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      hd, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ (hdiag 0), one_mul]
  refine ⟨proj 3 F Nsl, mem_map_of_mem _ hNu, ?_⟩
  rw [hσ, map_one, mul_one, hAeq, map_mul, conjAut_scalar, one_mul, conjAut_toGL]

end Coordinates

section Parabolics

variable {F : Type} [Field F]

theorem projUpperTriangular_le_projStabilizer_flag (d : ℕ) :
    projUpperTriangular 3 F ≤ projStabilizer (flagSpace 3 F d) := by
  rw [projUpperTriangular, projStabilizer, ← flagStabilizer_singleton]
  exact map_mono (upperTriangular_le_flagStabilizer {d})

theorem projStabilizer_inf_eq_projUpperTriangular :
    projStabilizer (flagSpace 3 F 1) ⊓ projStabilizer (flagSpace 3 F 2) =
      projUpperTriangular 3 F := by
  apply le_antisymm
  · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    have hst : s ∈ stabilizer (flagSpace 3 F 2) := by
      have h1 : t⁻¹ * s ∈ scalars 3 F := proj_eq_proj_iff.1 hts
      have h2 : s = t * (t⁻¹ * s) := by group
      rw [h2]
      exact mul_mem ht (scalars_le_stabilizer _ h1)
    refine ⟨s, fun i j hij => ?_, rfl⟩
    have hd : s ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1)) := by
      rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h | h
      · rw [h]; exact hs
      · rw [h]; exact hst
    have hv : (s : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 ∈ flagSpace 3 F ((j : ℕ) + 1) := by
      rw [← mem_stabilizer.1 hd]
      refine ⟨Pi.single j 1, mem_flagSpace.2 fun k hk => ?_, rfl⟩
      rw [Pi.single_eq_of_ne (fun h => by rw [h] at hk; omega)]
    have h3 := mem_flagSpace.1 hv i (by omega)
    rwa [mulVec_single_one, col_apply] at h3
  · exact le_inf (projUpperTriangular_le_projStabilizer_flag 1)
      (projUpperTriangular_le_projStabilizer_flag 2)

theorem projUpperTriangular_ne_top : projUpperTriangular 3 F ≠ ⊤ := by
  intro h
  have h1 : projStabilizer (flagSpace 3 F 1) = ⊤ := by
    rw [eq_top_iff, ← h]
    exact projUpperTriangular_le_projStabilizer_flag 1
  refine CFSG.QuasithinUnique.Setup.X7Sec.not_normal_projStabilizer_flag (K := F) (n := 3)
    (d := 1) (by norm_num) (by norm_num) ?_
  rw [h1]
  infer_instance

theorem finrank_coordImage {n : ℕ} (σ : F ≃+* F) (W : Submodule F (Fin n → F)) :
    Module.finrank F (coordImage σ W) = Module.finrank F W := by
  let j : W ≃+ coordImage σ W :=
    { toFun := fun w => ⟨fun i => σ (w.1 i), coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => σ.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (σ : F → F) j σ.bijective (fun r w => by ext i; simp [j])
  rw [Module.finrank, Module.finrank, h]

theorem map_projStabilizer_of_typeExchanging (D : GL (Fin 3) F) (σ : F ≃+* F)
    (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (conjAut 3 F D * fieldAut 3 F σ * dualAut 3 F).toMonoidHom =
      projStabilizer ((coordImage σ (dotOrth W)).map
        (mulVecLin (D : Matrix (Fin 3) (Fin 3) F))) ∧
    Module.finrank F ((coordImage σ (dotOrth W)).map
        (mulVecLin (D : Matrix (Fin 3) (Fin 3) F))) = 3 - Module.finrank F W := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (conjAut 3 F B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : F ≃+* F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (fieldAut 3 F τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    fun τ W => htrans.2.2.2.2.2.2.2.1 τ W
  have h9 : ∀ W : Submodule F (Fin 3 → F),
      (projStabilizer W).map (dualAut 3 F).toMonoidHom = projStabilizer (dotOrth W) :=
    fun W => htrans.2.2.2.2.2.2.2.2.1 W
  refine ⟨?_, ?_⟩
  · rw [CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, h9, h8, h7]
  · rw [CFSG.QuasithinUnique.Setup.Family.finrank_map_mulVecLin_gl, finrank_coordImage,
      finrank_dotOrth]

end Parabolics

section Inner

variable {G : Type*} [Group G]

theorem aut_mul_conj_mul_inv (s : MulAut G) (x : G) :
    s * MulAut.conj x * s⁻¹ = MulAut.conj (s x) := by
  ext m
  simp [MulAut.conj_apply]

theorem apply_mem_of_mem_normalizer_conj
    (hι : Function.Injective (MulAut.conj : G →* MulAut G)) {X : Subgroup G} {e : MulAut G}
    (he : e ∈ normalizer ((X.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) :
      Set (MulAut G))) {x : G} (hx : x ∈ X) : e x ∈ X := by
  have h1 := (mem_normalizer_iff.1 he (MulAut.conj x)).1 (mem_map_of_mem _ hx)
  rw [aut_mul_conj_mul_inv] at h1
  exact (mem_map_iff_mem hι).1 h1

theorem map_eq_of_mem_normalizer_conj
    (hι : Function.Injective (MulAut.conj : G →* MulAut G)) {X : Subgroup G} {e : MulAut G}
    (he : e ∈ normalizer ((X.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) :
      Set (MulAut G))) : X.map e.toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_of_mem_normalizer_conj hι he hx
  · intro x hx
    refine ⟨e⁻¹ x, apply_mem_of_mem_normalizer_conj hι (inv_mem he) hx, ?_⟩
    show e (e⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have h2 : y = x := by simpa using h1
    rwa [← h2]

theorem map_conj_map_conj (X : Subgroup G) (k : G) :
    (X.map (MulAut.conj : G →* MulAut G)).map (MulAut.conj (MulAut.conj k)).toMonoidHom =
      (X.map (MulAut.conj k).toMonoidHom).map (MulAut.conj : G →* MulAut G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun u => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]

theorem forall_mem_map_iff_central {H : Type*} [Group H] {Z U : Subgroup G}
    (h : ∀ x, x ∈ Z ↔ x ∈ U ∧ ∀ y ∈ U, x * y = y * x) (f : G →* H)
    (hf : Function.Injective f) (x : H) :
    x ∈ Z.map f ↔ x ∈ U.map f ∧ ∀ y ∈ U.map f, x * y = y * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzU, hzc⟩ := (h z).1 hz
    refine ⟨mem_map_of_mem _ hzU, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, hzc u hu]
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    refine mem_map_of_mem _ ((h u).2 ⟨hu, fun y hy => hf ?_⟩)
    have h1 := hc (f y) (mem_map_of_mem _ hy)
    rw [← map_mul, ← map_mul] at h1
    exact h1

theorem map_conj_inv_map_conj (Y : Subgroup G) (c : G) :
    (Y.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = Y := by
  rw [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, ← map_mul, mul_inv_cancel,
    map_one]
  ext y
  simp

theorem config_map_conj [Finite G] {I A R B : Subgroup G} [I.Normal] {x : G} (hxA : x ∈ A)
    (hKR : I ⊔ R = A) (hR : IsSylowOf 2 R A) (hRB : R ≤ B) (hBA : B < A)
    (hBmax : ∀ Y : Subgroup G, R ≤ Y → Y < A → Y ≤ B) :
    I ⊔ R.map (MulAut.conj x).toMonoidHom = A ∧ IsSylowOf 2 (R.map (MulAut.conj x).toMonoidHom) A ∧
      R.map (MulAut.conj x).toMonoidHom ≤ B.map (MulAut.conj x).toMonoidHom ∧
      B.map (MulAut.conj x).toMonoidHom < A ∧
      ∀ Y : Subgroup G, R.map (MulAut.conj x).toMonoidHom ≤ Y → Y < A →
        Y ≤ B.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hinv : ∀ Y : Subgroup G,
      (Y.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x)⁻¹.toMonoidHom = Y := fun Y => by
    rw [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, inv_mul_cancel]
    ext y
    simp
  have hmapN : ∀ {N : Subgroup G} {g : G}, g ∈ normalizer (N : Set G) →
      N.map (MulAut.conj g).toMonoidHom = N := by
    intro N g hg
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hg y).1 hy
    · intro y hy
      refine ⟨g⁻¹ * y * g, (mem_normalizer_iff.1 hg _).2 (by simpa [mul_assoc] using hy), ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  have hAφ : A.map (MulAut.conj x).toMonoidHom = A := hmapN (le_normalizer hxA)
  have hIφ : I.map (MulAut.conj x).toMonoidHom = I := hmapN (by
    rw [normalizer_eq_top I]
    exact mem_top x)
  have hAφ' : A.map (MulAut.conj x)⁻¹.toMonoidHom = A := by
    conv_lhs => rw [← hAφ]
    exact hinv A
  refine ⟨?_, ?_, map_mono hRB, ?_, ?_⟩
  · conv_lhs => rw [← hIφ]
    rw [← Subgroup.map_sup, hKR, hAφ]
  · have h := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective _ hinj hR
    rwa [hAφ] at h
  · rw [← hAφ]
    exact (map_lt_map_iff_of_injective hinj).2 hBA
  · intro Y hRY hYA
    have h1 : R ≤ Y.map (MulAut.conj x)⁻¹.toMonoidHom := by
      rw [← hinv R]
      exact map_mono hRY
    have h2 : Y.map (MulAut.conj x)⁻¹.toMonoidHom < A := by
      rw [← hAφ']
      exact (map_lt_map_iff_of_injective (MulAut.conj x)⁻¹.injective).2 hYA
    have h3 := map_mono (f := (MulAut.conj x).toMonoidHom) (hBmax _ h1 h2)
    rwa [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, mul_inv_cancel,
      show Y.map (1 : MulAut G).toMonoidHom = Y by ext y; simp] at h3

end Inner

section Main

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {F : Type} [Field F]

theorem le_normalizer_inf_inner {S X : Subgroup (MulAut (projectiveSL 3 F))}
    (hSX : S ≤ normalizer (X : Set (MulAut (projectiveSL 3 F)))) :
    S ≤ normalizer ((X ⊓ inner (projectiveSL 3 F) : Subgroup _) :
      Set (MulAut (projectiveSL 3 F))) :=
  le_normalizer_of_forall_conj_mem fun s hs y hy =>
    mem_inf.2 ⟨(mem_normalizer_iff.1 (hSX hs) y).1 (mem_inf.1 hy).1,
      (inner_normal _).conj_mem y (mem_inf.1 hy).2 s⟩

theorem exists_typeExchanging_mem [Finite F] [CharP F 2]
    {A R B : Subgroup (MulAut (projectiveSL 3 F))}
    (hKR : inner (projectiveSL 3 F) ⊔ R = A) (hR : IsSylowOf 2 R A) (hBA : B < A)
    (hBmax : ∀ Y : Subgroup (MulAut (projectiveSL 3 F)), R ≤ Y → Y < A → Y ≤ B) :
    ∃ r ∈ R, r ∉ semilinearAutGroup 3 F := by
  by_contra hcon
  push Not at hcon
  have hKA : inner (projectiveSL 3 F) ≤ A := hKR ▸ le_sup_left
  have hAs : A ≤ semilinearAutGroup 3 F := by
    rw [← hKR]
    refine sup_le ?_ fun r hr => hcon r hr
    exact (standard_outer_quotients (n := 3) (K := F)).1.trans
      linearAutGroup_le_semilinearAutGroup
  obtain ⟨Y₁, Y₂, h1, h2, h3, h4, h5⟩ :=
    CFSG.QuasithinUnique.Setup.X7Sec.hasTwoGeneratingOvergroups_of_le_semilinear hKA hAs
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hR)
  have h6 := sup_le (hBmax Y₁ h1 h3) (hBmax Y₂ h2 h4)
  rw [h5] at h6
  exact lt_irrefl A (lt_of_le_of_lt h6 hBA)

theorem isSylowOf_exists_map_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P P' D : Subgroup G} (hP : IsSylowOf p P D) (hP' : IsSylowOf p P' D) :
    ∃ x ∈ D, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q Q'
  refine ⟨d, d.2, ?_⟩
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

theorem standard_position_confinement [Finite F] [CharP F 2]
    {A R B : Subgroup (MulAut (projectiveSL 3 F))}
    (hKR : inner (projectiveSL 3 F) ⊔ R = A) (hR : IsSylowOf 2 R A) (hRB : R ≤ B) (hBA : B < A)
    (hBmax : ∀ Y : Subgroup (MulAut (projectiveSL 3 F)), R ≤ Y → Y < A → Y ≤ B)
    (hU : R ⊓ inner (projectiveSL 3 F) = (projUnitriangular 3 F).map MulAut.conj) :
    B = A ⊓ normalizer (((projUnitriangular 3 F).map MulAut.conj :
      Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) ∧
    B ⊓ inner (projectiveSL 3 F) = (projUpperTriangular 3 F).map MulAut.conj ∧
    ∀ E : Subgroup (MulAut (projectiveSL 3 F)), E ≤ R →
      R ≤ normalizer (E : Set (MulAut (projectiveSL 3 F))) → IsElementaryAbelian 2 ↥E →
        E ≤ ((uniCenter F).map (proj 3 F)).map MulAut.conj := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hι : Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) :=
    conj_injective_projectiveSL
  have hKA : inner (projectiveSL 3 F) ≤ A := hKR ▸ le_sup_left
  have hRA : R ≤ A := hR.le
  have hRN : R ≤ normalizer (((projUnitriangular 3 F).map MulAut.conj :
      Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) := by
    rw [← hU]
    exact le_normalizer_inf_inner le_normalizer
  obtain ⟨r, hrR, hrs⟩ := exists_typeExchanging_mem hKR hR hBA hBmax
  have hrU : (projUnitriangular 3 F).map r.toMonoidHom = projUnitriangular 3 F :=
    map_eq_of_mem_normalizer_conj hι (hRN hrR)
  have hNU := normalizer_projUnitriangular (K := F) (n := 3) 2
  have hBorelN : (projUpperTriangular 3 F).map MulAut.conj ≤ normalizer
      (((projUnitriangular 3 F).map MulAut.conj : Subgroup (MulAut (projectiveSL 3 F))) :
        Set (MulAut (projectiveSL 3 F))) := by
    refine le_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨b, hb, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [← hNU] at hb
    refine ⟨b * u * b⁻¹, (mem_normalizer_iff.1 hb u).1 hu, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hNB : A ⊓ normalizer (((projUnitriangular 3 F).map MulAut.conj :
      Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) ≤ B := by
    refine hBmax _ (le_inf hRA hRN) (lt_of_le_of_ne inf_le_left fun h => ?_)
    apply projUpperTriangular_ne_top (F := F)
    rw [← hNU, eq_top_iff]
    intro p _
    have h1 : MulAut.conj p ∈ A ⊓ normalizer (((projUnitriangular 3 F).map MulAut.conj :
        Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) := by
      rw [h]
      exact hKA ⟨p, rfl⟩
    exact mem_normalizer_of_map_conj_eq (map_eq_of_mem_normalizer_conj hι (mem_inf.1 h1).2)
  have hBI : B ⊓ inner (projectiveSL 3 F) < inner (projectiveSL 3 F) := by
    refine lt_of_le_of_ne inf_le_right fun h => ?_
    have h1 : A ≤ B := by
      rw [← hKR]
      refine sup_le ?_ hRB
      rw [← h]
      exact inf_le_left
    exact lt_irrefl A (lt_of_le_of_lt h1 hBA)
  set Y := (B ⊓ inner (projectiveSL 3 F)).comap
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) with hYdef
  have hYmap : Y.map MulAut.conj = B ⊓ inner (projectiveSL 3 F) :=
    map_comap_eq_self inf_le_right
  have hUY : projUnitriangular 3 F ≤ Y := fun u hu => by
    have h1 : MulAut.conj u ∈ R ⊓ inner (projectiveSL 3 F) := by
      rw [hU]
      exact mem_map_of_mem _ hu
    exact mem_inf.2 ⟨hRB (mem_inf.1 h1).1, (mem_inf.1 h1).2⟩
  have hYtop : Y ≠ ⊤ := by
    intro h
    apply hBI.ne
    rw [← hYmap, h, ← MonoidHom.range_eq_map]
    rfl
  obtain ⟨i, hi1, hi3, hYi⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (K := F) (n := 3)).2 Y hYtop hUY
  have hrY : Y.map r.toMonoidHom = Y := by
    refine map_eq_of_mem_normalizer_conj hι ?_
    rw [hYmap]
    exact le_normalizer_inf_inner le_normalizer (hRB hrR)
  obtain ⟨D, σ, hrD⟩ := exists_formula_of_not_mem_semilinear hrs
  obtain ⟨hW1, hW2⟩ := map_projStabilizer_of_typeExchanging D σ (flagSpace 3 F i)
  set W' := (coordImage σ (dotOrth (flagSpace 3 F i))).map
    (mulVecLin (D : Matrix (Fin 3) (Fin 3) F)) with hW'
  have hYW' : Y ≤ projStabilizer W' := by
    calc Y = Y.map r.toMonoidHom := hrY.symm
      _ ≤ (projStabilizer (flagSpace 3 F i)).map r.toMonoidHom := map_mono hYi
      _ = projStabilizer W' := by rw [hrD]; exact hW1
  have hW'eq := CFSG.QuasithinUnique.Setup.X7Sec.projStabilizer_eq_flag_of_le (hUY.trans hYW')
  rw [hW2, finrank_flagSpace (by omega)] at hW'eq
  rw [hW'eq] at hYW'
  have hYB : Y ≤ projUpperTriangular 3 F := by
    rw [← projStabilizer_inf_eq_projUpperTriangular]
    interval_cases i
    · exact le_inf hYi hYW'
    · exact le_inf hYW' hYi
  have hBIeq : B ⊓ inner (projectiveSL 3 F) = (projUpperTriangular 3 F).map MulAut.conj := by
    apply le_antisymm
    · rw [← hYmap]
      exact map_mono hYB
    · exact le_inf ((le_inf ((Subgroup.map_le_range _ _).trans hKA) hBorelN).trans hNB)
        (Subgroup.map_le_range _ _)
  have hBeq : B = A ⊓ normalizer (((projUnitriangular 3 F).map MulAut.conj :
      Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) := by
    refine le_antisymm (fun x hx => ?_) hNB
    have hxA : x ∈ R ⊔ inner (projectiveSL 3 F) := by
      rw [sup_comm, hKR]
      exact hBA.le hx
    obtain ⟨z, hz, y, hy, rfl⟩ := mem_sup_of_normal_right.1 hxA
    have hyB : y ∈ B := by
      have h1 := mul_mem (inv_mem (hRB hz)) hx
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
    have hyN : y ∈ (projUpperTriangular 3 F).map MulAut.conj := by
      rw [← hBIeq]
      exact mem_inf.2 ⟨hyB, hy⟩
    exact mem_inf.2 ⟨hBA.le hx, mul_mem (hRN hz) (hBorelN hyN)⟩
  refine ⟨hBeq, hBIeq, fun E hER hRE hE => ?_⟩
  have hE2 : ∀ g ∈ E, g * g = 1 := fun g hg => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) g hg
    rwa [pow_two] at h1
  have hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hE.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  set YE := (E ⊓ inner (projectiveSL 3 F)).comap
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) with hYEdef
  have hYEmap : YE.map MulAut.conj = E ⊓ inner (projectiveSL 3 F) :=
    map_comap_eq_self inf_le_right
  have hYEU : YE ≤ projUnitriangular 3 F := fun g hg => by
    have h1 : MulAut.conj g ∈ R ⊓ inner (projectiveSL 3 F) :=
      mem_inf.2 ⟨hER (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩
    rw [hU] at h1
    exact (mem_map_iff_mem hι).1 h1
  have hYE2 : ∀ g ∈ YE, g * g = 1 := fun g hg => hι (by
    rw [map_mul, map_one]
    exact hE2 _ (mem_inf.1 hg).1)
  have hYEc : ∀ g ∈ YE, ∀ h ∈ YE, g * h = h * g := fun g hg h hh => hι (by
    rw [map_mul, map_mul]
    exact hEc _ (mem_inf.1 hg).1 _ (mem_inf.1 hh).1)
  have hrYE : YE.map r.toMonoidHom = YE := by
    refine map_eq_of_mem_normalizer_conj hι ?_
    rw [hYEmap]
    exact le_normalizer_inf_inner hRE hrR
  have hYEZ : YE ≤ (uniCenter F).map (proj 3 F) := by
    rw [← projRad_inf_eq]
    rcases le_projRad_of_elementary hYEU hYE2 hYEc with h | h
    · refine le_inf h ?_
      calc YE = YE.map r.toMonoidHom := hrYE.symm
        _ ≤ ((uniRadOne F).map (proj 3 F)).map r.toMonoidHom := map_mono h
        _ ≤ _ := map_uniRadOne_le_of_not_mem_semilinear hrU hrs
    · refine le_inf ?_ h
      calc YE = YE.map r.toMonoidHom := hrYE.symm
        _ ≤ ((uniRadTwo F).map (proj 3 F)).map r.toMonoidHom := map_mono h
        _ ≤ _ := map_uniRadTwo_le_of_not_mem_semilinear hrU hrs
  intro e he
  have heU : (projUnitriangular 3 F).map e.toMonoidHom = projUnitriangular 3 F :=
    map_eq_of_mem_normalizer_conj hι (hRN (hER he))
  have htriv : ∀ u ∈ projUnitriangular 3 F, e u * u⁻¹ ∈ (uniCenter F).map (proj 3 F) := by
    intro u hu
    apply hYEZ
    show MulAut.conj (e u * u⁻¹) ∈ E ⊓ inner (projectiveSL 3 F)
    have hcomm : MulAut.conj (e u * u⁻¹) =
        e * (MulAut.conj u * e⁻¹ * (MulAut.conj u)⁻¹) := by
      rw [map_mul, map_inv, ← aut_mul_conj_mul_inv]
      group
    have huR : MulAut.conj u ∈ R := by
      have h1 : MulAut.conj u ∈ R ⊓ inner (projectiveSL 3 F) := by
        rw [hU]
        exact mem_map_of_mem _ hu
      exact (mem_inf.1 h1).1
    refine mem_inf.2 ⟨?_, ⟨_, rfl⟩⟩
    rw [hcomm]
    exact mul_mem he ((mem_normalizer_iff.1 (hRE huR) _).1 (inv_mem he))
  obtain ⟨v, -, hev⟩ := exists_eq_conj_of_trivial_mod_center heU htriv
  have heI : e ∈ E ⊓ inner (projectiveSL 3 F) := mem_inf.2 ⟨he, ⟨v, hev.symm⟩⟩
  rw [← hYEmap] at heI
  obtain ⟨w, hw, rfl⟩ := heI
  exact mem_map_of_mem _ (hYEZ hw)

theorem qrc_linear_three_diagram_actors_confine_normal_elementary_subgroups_to_the_central_root
    {f : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    {A R B : Subgroup (MulAut (projectiveSL 3 F))} (hR : IsSylowOf 2 R A)
    (hKR : inner (projectiveSL 3 F) ⊔ R = A) (hRB : R ≤ B) (hBA : B < A)
    (hBmax : ∀ Y : Subgroup (MulAut (projectiveSL 3 F)), R ≤ Y → Y < A → Y ≤ B) :
    (∃ r ∈ R, (∃ (D : GL (Fin 3) F) (σ : F ≃+* F),
        r = conjAut 3 F D * fieldAut 3 F σ * dualAut 3 F) ∧
      ∀ W : Submodule F (Fin 3 → F), ∃ W' : Submodule F (Fin 3 → F),
        Module.finrank F W' = 3 - Module.finrank F W ∧
          (projStabilizer W).map r.toMonoidHom = projStabilizer W') ∧
    ∃ k : projectiveSL 3 F,
      R ⊓ inner (projectiveSL 3 F) =
        ((projUnitriangular 3 F).map (MulAut.conj k).toMonoidHom).map MulAut.conj ∧
      B = A ⊓ normalizer ((R ⊓ inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :
        Set (MulAut (projectiveSL 3 F))) ∧
      B ⊓ inner (projectiveSL 3 F) =
        ((projUpperTriangular 3 F).map (MulAut.conj k).toMonoidHom).map MulAut.conj ∧
      (∀ x, x ∈ (((uniCenter F).map (proj 3 F)).map (MulAut.conj k).toMonoidHom).map
          MulAut.conj ↔ x ∈ R ⊓ inner (projectiveSL 3 F) ∧
            ∀ y ∈ R ⊓ inner (projectiveSL 3 F), x * y = y * x) ∧
      ∀ E : Subgroup (MulAut (projectiveSL 3 F)), E ≤ R →
        R ≤ normalizer (E : Set (MulAut (projectiveSL 3 F))) → IsElementaryAbelian 2 ↥E →
          E ≤ (((uniCenter F).map (proj 3 F)).map (MulAut.conj k).toMonoidHom).map
            MulAut.conj ∧ E ≤ inner (projectiveSL 3 F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hι : Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) :=
    conj_injective_projectiveSL
  have hKA : inner (projectiveSL 3 F) ≤ A := hKR ▸ le_sup_left
  obtain ⟨r, hrR, hrs⟩ := exists_typeExchanging_mem hKR hR hBA hBmax
  obtain ⟨D, σ, hrD⟩ := exists_formula_of_not_mem_semilinear hrs
  refine ⟨⟨r, hrR, ⟨D, σ, hrD⟩, fun W => ⟨_, (map_projStabilizer_of_typeExchanging D σ W).2,
    by rw [hrD]; exact (map_projStabilizer_of_typeExchanging D σ W).1⟩⟩, ?_⟩
  have hAI : A ≤ normalizer ((inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :
      Set (MulAut (projectiveSL 3 F))) := by
    rw [normalizer_eq_top (inner (projectiveSL 3 F))]
    exact le_top
  have hRI := hR.inf_of_le_normalizer hKA hAI
  have hUI : IsSylowOf 2 ((projUnitriangular 3 F).map MulAut.conj)
      (inner (projectiveSL 3 F)) := by
    obtain ⟨Pu, hPu⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
    have h1 : IsSylowOf 2 (projUnitriangular 3 F) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, ?_, ?_⟩
      · rw [← hPu]
        exact Pu.isPGroup'
      · rw [relIndex_top_right, ← hPu]
        exact Pu.not_dvd_index
    have h2 := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective _ hι h1
    rwa [← MonoidHom.range_eq_map] at h2
  obtain ⟨x, hxI, hx⟩ := isSylowOf_exists_map_conj hUI hRI
  obtain ⟨k, rfl⟩ := hxI
  refine ⟨k, hx.trans (map_conj_map_conj _ k), ?_⟩
  set c : MulAut (projectiveSL 3 F) := MulAut.conj k with hc
  have hcA : c⁻¹ ∈ A := inv_mem (hKA ⟨k, rfl⟩)
  obtain ⟨hKR', hR', hRB', hBA', hBmax'⟩ :=
    config_map_conj (I := inner (projectiveSL 3 F)) hcA hKR hR hRB hBA hBmax
  have hIc : ∀ g : MulAut (projectiveSL 3 F),
      (inner (projectiveSL 3 F)).map (MulAut.conj g).toMonoidHom = inner (projectiveSL 3 F) :=
    fun g => by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact (inner_normal _).conj_mem y hy g
      · intro y hy
        refine ⟨g⁻¹ * y * g, ?_, ?_⟩
        · have h1 := (inner_normal _).conj_mem y hy g⁻¹
          rwa [inv_inv] at h1
        · show g * (g⁻¹ * y * g) * g⁻¹ = y
          group
  have hAc : A.map (MulAut.conj c).toMonoidHom = A := by
    have hcA' : c ∈ A := hKA ⟨k, rfl⟩
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hcA' hy) (inv_mem hcA')
    · intro y hy
      refine ⟨c⁻¹ * y * c, mul_mem (mul_mem hcA hy) hcA', ?_⟩
      show c * (c⁻¹ * y * c) * c⁻¹ = y
      group
  have hinjc : ∀ g : MulAut (projectiveSL 3 F),
      Function.Injective (MulAut.conj g).toMonoidHom := fun g => (MulAut.conj g).injective
  have hU' : R.map (MulAut.conj c⁻¹).toMonoidHom ⊓ inner (projectiveSL 3 F) =
      (projUnitriangular 3 F).map MulAut.conj := by
    conv_lhs => rw [← hIc c⁻¹]
    rw [← map_inf_eq _ _ _ (hinjc _), hx, ← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      ← map_mul, inv_mul_cancel, map_one]
    ext y
    simp
  obtain ⟨hB', hBI', hE'⟩ := standard_position_confinement hKR' hR' hRB' hBA' hBmax' hU'
  have hback : ∀ Y : Subgroup (MulAut (projectiveSL 3 F)),
      (Y.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = Y :=
    fun Y => map_conj_inv_map_conj Y c
  have hZk : (((uniCenter F).map (proj 3 F)).map MulAut.conj).map (MulAut.conj c).toMonoidHom =
      (((uniCenter F).map (proj 3 F)).map (MulAut.conj k).toMonoidHom).map MulAut.conj :=
    map_conj_map_conj _ k
  refine ⟨?_, ?_, ?_, fun E hER hRE hE => ?_⟩
  ·
    rw [← hback B, hB', map_inf_eq _ _ _ (hinjc c), hAc,
      Subgroup.map_equiv_normalizer_eq _ (MulAut.conj c), hx]
  ·
    rw [← map_conj_map_conj, ← hBI', map_inf_eq _ _ _ (hinjc c), hback B, hIc c]
  ·
    intro y
    rw [← hZk, hx]
    refine forall_mem_map_iff_central (fun z => ?_) _ (hinjc c) y
    exact forall_mem_map_iff_central (fun g => mem_projCenter_iff) _ hι z
  ·
    have hE2 : IsElementaryAbelian 2 ↥(E.map (MulAut.conj c⁻¹).toMonoidHom) := by
      have := hE
      exact IsElementaryAbelian.map _
    have hRE' : R.map (MulAut.conj c⁻¹).toMonoidHom ≤
        normalizer ((E.map (MulAut.conj c⁻¹).toMonoidHom : Subgroup (MulAut (projectiveSL 3 F))) :
          Set (MulAut (projectiveSL 3 F))) := by
      rw [← Subgroup.map_equiv_normalizer_eq _ (MulAut.conj c⁻¹)]
      exact map_mono hRE
    have h1 := map_mono (f := (MulAut.conj c).toMonoidHom) (hE' _ (map_mono hER) hRE' hE2)
    rw [hback E, hZk] at h1
    exact ⟨h1, h1.trans (Subgroup.map_le_range _ _)⟩

end Main


end CFSG.Quasithin.SteinbergBS
