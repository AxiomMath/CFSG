module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem diag_conj_of_upper {X T : SpecialLinearGroup (Fin 3) K} (hX : X ∈ upperTriangular 3 K)
    (hT : T ∈ upperTriangular 3 K) (i : Fin 3) :
    ((X * T * X⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i =
      (T : Matrix (Fin 3) (Fin 3) K) i i := by
  have hX' := mem_upperTriangular_iff_isUpperTriangular.mp hX
  have hT' := mem_upperTriangular_iff_isUpperTriangular.mp hT
  have hXi := coe_inv_isUpperTriangular hX'
  change ((X : Matrix (Fin 3) (Fin 3) K) * (T : Matrix (Fin 3) (Fin 3) K) *
    ((X⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i = _
  rw [mul_apply_self_of_isUpperTriangular (hX'.mul hT') hXi,
    mul_apply_self_of_isUpperTriangular hX' hT', mul_comm _ ((T : Matrix (Fin 3) (Fin 3) K) i i),
    mul_assoc, coe_inv_apply_self_of_isUpperTriangular hX' i, mul_one]

theorem mul_inv_mem_unitriangular {Y Z : SpecialLinearGroup (Fin 3) K}
    (hY : Y ∈ upperTriangular 3 K) (hZ : Z ∈ upperTriangular 3 K)
    (h : ∀ i, (Y : Matrix (Fin 3) (Fin 3) K) i i = (Z : Matrix (Fin 3) (Fin 3) K) i i) :
    Y * Z⁻¹ ∈ unitriangular 3 K := by
  refine ⟨(upperTriangular 3 K).mul_mem hY ((upperTriangular 3 K).inv_mem hZ), fun i => ?_⟩
  have hY' := mem_upperTriangular_iff_isUpperTriangular.mp hY
  have hZ' := mem_upperTriangular_iff_isUpperTriangular.mp hZ
  change ((Y : Matrix (Fin 3) (Fin 3) K) *
    ((Z⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i = 1
  rw [mul_apply_self_of_isUpperTriangular hY' (coe_inv_isUpperTriangular hZ'), h i,
    coe_inv_apply_self_of_isUpperTriangular hZ' i]

theorem w_mul_mul_w_apply (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (!![0, 0, 1; 0, 1, 0; 1, 0, 0] * M * !![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K)
      i j = M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, Fin.rev]

@[expose] noncomputable def torusM (ζ : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(ζ : K), 1, ((ζ⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem coe_torusM (ζ : Kˣ) :
    ((torusM ζ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(ζ : K), 1, ((ζ⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def torusMSL : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun := torusM
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal ![((1 : Kˣ) : K), 1, (((1 : Kˣ)⁻¹ : Kˣ) : K)] = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' ζ η := by
    apply Subtype.ext
    change Matrix.diagonal ![((ζ * η : Kˣ) : K), 1, (((ζ * η)⁻¹ : Kˣ) : K)] =
      Matrix.diagonal ![(ζ : K), 1, ((ζ⁻¹ : Kˣ) : K)] *
        Matrix.diagonal ![(η : K), 1, ((η⁻¹ : Kˣ) : K)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

@[expose] noncomputable def torusMHom : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp torusMSL

theorem torusMHom_injective : Function.Injective (torusMHom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro ζ hζ
  rw [MonoidHom.mem_ker] at hζ
  change QuotientGroup.mk' (scalars 3 K) (torusMSL ζ) = 1 at hζ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hζ
  obtain ⟨c, -, hc⟩ := hζ
  change ((torusM ζ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _ at hc
  rw [coe_torusM] at hc
  have h1 := congrFun (congrFun hc 1) 1
  have h0 := congrFun (congrFun hc 0) 0
  simp at h1 h0
  rw [Subgroup.mem_bot]
  apply Units.ext
  rw [h0, ← h1, Units.val_one]

theorem torusM_mem_upper (ζ : Kˣ) : torusM ζ ∈ upperTriangular 3 K := by
  intro i j hij
  rw [coe_torusM, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]

variable [CharP K 2]

@[expose] noncomputable def wSL : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    rw [Matrix.det_fin_three]
    simp [CharTwo.neg_eq]⟩

theorem wSL_mul_self : (wSL : SpecialLinearGroup (Fin 3) K) * wSL = 1 := by
  apply Subtype.ext
  change (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem wSL_inv : (wSL : SpecialLinearGroup (Fin 3) K)⁻¹ = wSL :=
  inv_eq_of_mul_eq_one_right wSL_mul_self

@[expose] noncomputable def thetaAut : MulAut (projectiveSL 3 K) :=
  MulAut.conj (proj 3 K wSL) * dualAut 3 K

theorem thetaAut_proj (g : SpecialLinearGroup (Fin 3) K) :
    thetaAut (proj 3 K g) = proj 3 K (wSL * (g⁻¹).transpose * wSL) := by
  rw [thetaAut, MulAut.mul_apply, dualAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul,
    ← map_mul, wSL_inv]

theorem w_transpose_w_mem {v : SpecialLinearGroup (Fin 3) K} (hv : v ∈ unitriangular 3 K) :
    wSL * v.transpose * wSL ∈ unitriangular 3 K := by
  obtain ⟨hv1, hv2⟩ := hv
  have key : ∀ i j, ((wSL * v.transpose * wSL : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = (v : Matrix (Fin 3) (Fin 3) K) (Fin.rev j) (Fin.rev i) := by
    intro i j
    change (((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
      (v : Matrix (Fin 3) (Fin 3) K)ᵀ * !![0, 0, 1; 0, 1, 0; 1, 0, 0] :
        Matrix (Fin 3) (Fin 3) K)) i j = _
    rw [w_mul_mul_w_apply, Matrix.transpose_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    exact hv1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [key]
    exact hv2 _

theorem thetaAut_mem {u : projectiveSL 3 K} (hu : u ∈ projUnitriangular 3 K) :
    thetaAut u ∈ projUnitriangular 3 K := by
  obtain ⟨v, hv, rfl⟩ := hu
  rw [thetaAut_proj]
  exact ⟨_, w_transpose_w_mem ((unitriangular 3 K).inv_mem hv), rfl⟩

theorem thetaAut_torusM (ζ : Kˣ) : thetaAut (torusMHom ζ) = torusMHom ζ := by
  change thetaAut (proj 3 K (torusM ζ)) = proj 3 K (torusM ζ)
  rw [thetaAut_proj]
  congr 1
  have hinv : (torusM ζ)⁻¹ = torusM ζ⁻¹ := by
    have := map_inv (torusMSL (K := K)) ζ
    exact this.symm
  rw [hinv]
  apply Subtype.ext
  change (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
    (Matrix.diagonal ![((ζ⁻¹ : Kˣ) : K), 1, (((ζ⁻¹)⁻¹ : Kˣ) : K)])ᵀ *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] = Matrix.diagonal ![(ζ : K), 1, ((ζ⁻¹ : Kˣ) : K)]
  ext i j
  rw [w_mul_mul_w_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.rev]

end BK10.L3

end CFSG.Quasithin.Vol2.Ch11.SecD
