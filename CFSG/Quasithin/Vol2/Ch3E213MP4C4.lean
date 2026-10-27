module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionUnitary

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction CFSG.GorensteinWalter
open scoped MatrixGroups

variable {K k₀ : Type} [Field K] [Field k₀]

@[expose] def sublineMatrix (ι : k₀ →+* K) (g : Matrix (Fin 2) (Fin 2) k₀) :
    Matrix (Fin 3) (Fin 3) K :=
  !![ι (g 0 0), 0, ι (g 0 1); 0, 1, 0; ι (g 1 0), 0, ι (g 1 1)]

theorem sublineMatrix_mul (ι : k₀ →+* K) (g h : Matrix (Fin 2) (Fin 2) k₀) :
    sublineMatrix ι (g * h) = sublineMatrix ι g * sublineMatrix ι h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sublineMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem sublineMatrix_one (ι : k₀ →+* K) : sublineMatrix ι 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sublineMatrix]

theorem sublineMatrix_injective (ι : k₀ →+* K) : Function.Injective (sublineMatrix ι) := by
  intro g h hgh
  have e : ∀ i j, sublineMatrix ι g i j = sublineMatrix ι h i j := fun i j => by rw [hgh]
  ext i j
  fin_cases i <;> fin_cases j
  · exact ι.injective (e 0 0)
  · exact ι.injective (e 0 2)
  · exact ι.injective (e 2 0)
  · exact ι.injective (e 2 2)

theorem sublineMatrix_coe_mul (ι : k₀ →+* K) (a b : SL(2, k₀)) :
    sublineMatrix ι ↑(a * b) = sublineMatrix ι ↑a * sublineMatrix ι ↑b :=
  sublineMatrix_mul ι _ _

theorem sublineMatrix_coe_one (ι : k₀ →+* K) : sublineMatrix ι ↑(1 : SL(2, k₀)) = 1 :=
  sublineMatrix_one ι

@[expose] def sublineGL (ι : k₀ →+* K) : SL(2, k₀) →* GL (Fin 3) K where
  toFun g := ⟨sublineMatrix ι g, sublineMatrix ι ↑g⁻¹,
    by rw [← sublineMatrix_coe_mul, mul_inv_cancel, sublineMatrix_coe_one],
    by rw [← sublineMatrix_coe_mul, inv_mul_cancel, sublineMatrix_coe_one]⟩
  map_one' := Units.ext (sublineMatrix_coe_one ι)
  map_mul' g h := Units.ext (sublineMatrix_coe_mul ι g h)

theorem sublineGL_val (ι : k₀ →+* K) (g : SL(2, k₀)) :
    (sublineGL ι g : Matrix (Fin 3) (Fin 3) K) = sublineMatrix ι g := rfl

theorem sublineGL_mem [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (ι : k₀ →+* K)
    (hι : ∀ x, J.conj (ι x) = ι x) (g : SL(2, k₀)) : sublineGL ι g ∈ J.specialSubgroup := by
  have hdet : ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 0) * ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 1) -
      ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 1) * ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 0) = 1 := by
    have h := congrArg ι g.2
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
    exact h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine (J.mem_specialSubgroup_iff _).mpr ⟨?_, ?_⟩
  · rw [hJ, sublineGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, sublineMatrix, Matrix.mul_apply, Fin.sum_univ_three, hι]
    · linear_combination ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 0) *
        ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 0) * h2
    · linear_combination hdet + ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 1) *
        ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 0) * h2
    · linear_combination hdet + ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 1) *
        ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 0) * h2
    · linear_combination ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 1) *
        ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 1) * h2
  · ext
    rw [GeneralLinearGroup.val_det_apply, sublineGL_val, Units.val_one]
    simp [sublineMatrix, Matrix.det_fin_three]
    linear_combination hdet

@[expose] noncomputable def sublineHom [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (ι : k₀ →+* K)
    (hι : ∀ x, J.conj (ι x) = ι x) : SL(2, k₀) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjGenLinGroup.mk.comp (sublineGL ι)).codRestrict _
    fun g => Subgroup.mem_map_of_mem _ (sublineGL_mem J hJ ι hι g)

theorem isCoatom_stabilizer [Finite K] (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsCoatom (unitaryCoordinateStabilizer J 0) := by
  obtain ⟨-, -, -, -, -, rho, -, -, -, h2, hstab, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  let _ : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    MulAction.compHom _ rho
  have htwo : MulAction.IsMultiplyPretransitive (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryIsotropicPoints J) 2 :=
    MulAction.is_two_pretransitive_iff.mpr fun {a b c d} hab hcd => h2 a b c d hab hcd
  have : MulAction.IsPreprimitive (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryIsotropicPoints J) := MulAction.isPreprimitive_of_is_two_pretransitive htwo
  have : Nontrivial (unitaryIsotropicPoints J) :=
    ⟨⟨unitaryOuterIsotropicPoint J hJ 0 (by decide), unitaryOuterIsotropicPoint J hJ 2 (by decide),
      fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h).symm⟩⟩
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryOuterIsotropicPoint J hJ 0 (by decide))
  rwa [← hstab]

variable [CharP K 2] (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
  (ι : k₀ →+* K) (hι : ∀ x, J.conj (ι x) = ι x)

theorem sublineHom_val (g : SL(2, k₀)) :
    ((sublineHom J hJ ι hι g : ProjectiveSpecialUnitaryMatrixGroup J) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (sublineGL ι g) := rfl

theorem sublineHom_injective : Function.Injective (sublineHom J hJ ι hι) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h1 : ProjGenLinGroup.mk (sublineGL ι g) = 1 := by
    rw [← sublineHom_val J hJ ι hι, hg]
    rfl
  obtain ⟨c, hc, -, -⟩ := (special_mk_eq_one_iff J hJ (sublineGL_mem J hJ ι hι g)).mp h1
  rw [sublineGL_val] at hc
  have h11 := congrFun (congrFun hc 1) 1
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h11
  have hc1 : c = 1 := h11.symm
  rw [hc1, Matrix.scalar_apply, Matrix.diagonal_one, ← sublineMatrix_coe_one ι] at hc
  rw [Subgroup.mem_bot]
  exact Subtype.ext (sublineMatrix_injective ι hc)

theorem sublineHom_mem_stabilizer_iff (g : SL(2, k₀)) :
    sublineHom J hJ ι hι g ∈ unitaryCoordinateStabilizer J 0 ↔ g ∈ sl2Borel k₀ := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  change ProjGenLinGroup.mk (sublineGL ι g) • unitaryCoordinatePoint (K := K) 0 =
    unitaryCoordinatePoint (K := K) 0 ↔ _
  rw [unitary_projective_coordinate_maps_iff]
  constructor
  · intro h
    have h2 := h 2 (by decide)
    rw [sublineGL_val] at h2
    simpa [sublineMatrix] using h2
  · intro h k hk
    rw [sublineGL_val]
    fin_cases k
    · exact (hk rfl).elim
    · simp [sublineMatrix]
    · simp [sublineMatrix, h]

theorem sublineHom_upperUnipotent (x : k₀) :
    sublineHom J hJ ι hι (sl2UpperUnipotent x) =
      hermitianUnipotentPSU J hJ (centralCoord J (ι x) (hι x)) := by
  apply Subtype.ext
  rw [sublineHom_val, hermitianUnipotentPSU_val]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  rw [sublineGL_val, centralCoord_matrix]
  fin_cases i <;> fin_cases j <;> simp [sublineMatrix, sl2UpperUnipotent]

theorem sublineHom_mem_root_iff (g : SL(2, k₀)) :
    sublineHom J hJ ι hι g ∈ (hermitianUnipotentPSU J hJ).range ↔
      g ∈ sl2UpperUnipotentSubgroup k₀ := by
  rw [mem_sl2UpperUnipotentSubgroup_iff]
  constructor
  · intro h
    obtain ⟨a, b, M, -, hM, hgM⟩ := (mem_root_iff J hJ _).mp h
    rw [sublineHom_val] at hgM
    obtain ⟨c, -, hc⟩ := exists_smul_of_mk_eq hgM
    rw [hM, sublineGL_val] at hc
    have e11 : (1 : K) = c * 1 := congrFun (congrFun hc 1) 1
    rw [mul_one] at e11
    subst e11
    rw [one_smul] at hc
    have e00 : (1 : K) = ι ((g : Matrix (Fin 2) (Fin 2) k₀) 0 0) := congrFun (congrFun hc 0) 0
    have e20 : (0 : K) = ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 0) := congrFun (congrFun hc 2) 0
    have e22 : (1 : K) = ι ((g : Matrix (Fin 2) (Fin 2) k₀) 1 1) := congrFun (congrFun hc 2) 2
    have f00 := ι.injective ((map_one ι).trans e00)
    have f10 := ι.injective ((map_zero ι).trans e20)
    have f11 := ι.injective ((map_one ι).trans e22)
    refine ⟨(g : Matrix (Fin 2) (Fin 2) k₀) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent, ← f00, ← f10, ← f11]
  · rintro ⟨x, rfl⟩
    rw [sublineHom_upperUnipotent]
    exact ⟨_, rfl⟩

theorem exists_sublineHom_eq_of_involution [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hιs : ∀ b : K, J.conj b = b → ∃ b₀ : k₀, ι b₀ = b)
    {x : ProjectiveSpecialUnitaryMatrixGroup J} (hxB : x ∈ unitaryCoordinateStabilizer J 0)
    (hx2 : orderOf x = 2) :
    ∃ y ∈ sl2UpperUnipotentSubgroup k₀, sublineHom J hJ ι hι y = x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  obtain ⟨b, M, hb, -, hM, hxM⟩ := (hinv x).mp ⟨hxB, hx2⟩
  obtain ⟨b₀, rfl⟩ := hιs b (CharTwo.add_eq_zero.mp hb).symm
  refine ⟨sl2UpperUnipotent b₀, (mem_sl2UpperUnipotentSubgroup_iff _).mpr ⟨b₀, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [sublineHom_val, hxM]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  rw [sublineGL_val, hM]
  fin_cases i <;> fin_cases j <;> simp [sublineMatrix, sl2UpperUnipotent]

end CFSG.Quasithin.Ch3E213M.P4C
