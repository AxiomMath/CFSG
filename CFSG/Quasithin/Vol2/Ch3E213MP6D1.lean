module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4

public section

namespace CFSG.Quasithin.Ch3E213M.P6D

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.GorensteinWalter
open CFSG.QuasithinUnique.Fin257.Sp4
open scoped MatrixGroups

variable {k : Type} [Field k]

@[expose] def diagMat (g : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![g 0 0, 0, g 0 1, g 0 1; 0, g 0 0, 0, g 0 1; g 1 0, g 1 0, g 1 1, 0; 0, g 1 0, 0, g 1 1]

theorem diagMat_injective : Function.Injective (diagMat (k := k)) := by
  intro g h hgh
  have e : ∀ i j, diagMat g i j = diagMat h i j := fun i j => by rw [hgh]
  ext i j
  fin_cases i <;> fin_cases j
  · exact e 0 0
  · exact e 0 2
  · exact e 2 0
  · exact e 2 2

theorem diagMat_one : diagMat (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat]

theorem diagMat_coe_one : diagMat ((1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1 :=
  diagMat_one

variable [CharP k 2]

theorem diagMat_mul (g h : Matrix (Fin 2) (Fin 2) k) :
    diagMat (g * h) = diagMat g * diagMat h := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (g 0 1 * h 1 0) * h2
    | linear_combination (-(g 0 1 * h 1 0)) * h2
    | linear_combination (g 1 0 * h 0 1) * h2
    | linear_combination (-(g 1 0 * h 0 1)) * h2

theorem diagMat_coe_mul (a b : SL(2, k)) :
    diagMat ((a * b : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      diagMat (a : Matrix (Fin 2) (Fin 2) k) * diagMat (b : Matrix (Fin 2) (Fin 2) k) :=
  diagMat_mul _ _

theorem diagMat_mem (g : SL(2, k)) :
    (diagMat (g : Matrix (Fin 2) (Fin 2) k))ᵀ * minorJ k * diagMat (g : Matrix (Fin 2) (Fin 2) k) =
      minorJ k := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.2
  ext i j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases i <;> fin_cases j <;> simp [diagMat] <;>
    first
    | ring1
    | linear_combination ((g : Matrix (Fin 2) (Fin 2) k) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 0) * h2
    | linear_combination (-((g : Matrix (Fin 2) (Fin 2) k) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 0)) * h2
    | linear_combination ((g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 0) * h2
    | linear_combination (-((g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 0)) * h2
    | linear_combination ((g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 1) * h2
    | linear_combination (-((g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 1)) * h2
    | linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) k) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) k) 1 0) * h2

@[expose] def diagSL : SL(2, k) →* antiSp k where
  toFun g := ⟨⟨diagMat (g : Matrix (Fin 2) (Fin 2) k),
    diagMat ((g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k),
    by rw [← diagMat_coe_mul, mul_inv_cancel, diagMat_coe_one],
    by rw [← diagMat_coe_mul, inv_mul_cancel, diagMat_coe_one]⟩, diagMat_mem g⟩
  map_one' := antiSp_ext diagMat_coe_one
  map_mul' g h := antiSp_ext (diagMat_coe_mul g h)

theorem glMat_diagSL (g : SL(2, k)) :
    glMat (diagSL g : GL (Fin 4) k) = diagMat (g : Matrix (Fin 2) (Fin 2) k) := rfl

theorem diagSL_injective : Function.Injective (diagSL (k := k)) := fun _ _ hgh =>
  Subtype.ext (diagMat_injective (congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hgh))

theorem diagSL_upperUnipotent (t : k) : diagSL (sl2UpperUnipotent t) = uElt 0 t t 0 := by
  apply antiSp_ext
  rw [glMat_diagSL, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat, sl2UpperUnipotent, uMat]

theorem diagSL_mem_antiUnipotent_iff (g : SL(2, k)) :
    diagSL g ∈ antiUnipotent k ↔ g ∈ sl2UpperUnipotentSubgroup k := by
  rw [mem_sl2UpperUnipotentSubgroup_iff]
  constructor
  · intro h
    obtain ⟨hlow, hdiag⟩ := (mem_antiUnipotent_iff_upper _).mp h
    rw [glMat_diagSL] at hlow hdiag
    have h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := hlow 2 0 (by decide)
    have h00 : (g : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := hdiag 0
    have h11 : (g : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := hdiag 2
    refine ⟨(g : Matrix (Fin 2) (Fin 2) k) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent, h10, h00, h11]
  · rintro ⟨t, rfl⟩
    rw [diagSL_upperUnipotent]
    exact uElt_mem_antiUnipotent 0 t t 0

theorem diagSL_mem_normalizer {g : SL(2, k)} (hg : g ∈ sl2Borel k) :
    diagSL g ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff] at hg
  refine mem_normalizer_of_isUpper fun i j hij => ?_
  rw [glMat_diagSL]
  fin_cases i <;> fin_cases j <;> simp_all [diagMat]

@[expose] noncomputable def diagSLμ (μ : kˣ) : SL(2, k) →* antiSp k :=
  (MulAut.conj (dSp 1 μ : antiSp k)).toMonoidHom.comp diagSL

theorem diagSLμ_apply (μ : kˣ) (g : SL(2, k)) :
    diagSLμ μ g = dSp 1 μ * diagSL g * (dSp 1 μ)⁻¹ := rfl

theorem diagSLμ_injective (μ : kˣ) : Function.Injective (diagSLμ (k := k) μ) :=
  (MulAut.conj _).injective.comp diagSL_injective

theorem diagSLμ_upperUnipotent (μ : kˣ) (t : k) :
    diagSLμ μ (sl2UpperUnipotent t) = uElt 0 (t * μ) (t * 1) 0 := by
  rw [diagSLμ_apply, diagSL_upperUnipotent, dSp_conj_uElt]
  simp only [Units.val_one, one_mul, mul_zero, one_pow, mul_one, mul_comm (μ : k) t]

theorem diagSLμ_mem_antiUnipotent_iff (μ : kˣ) (g : SL(2, k)) :
    diagSLμ μ g ∈ antiUnipotent k ↔ g ∈ sl2UpperUnipotentSubgroup k := by
  rw [diagSLμ_apply, ← (Subgroup.mem_normalizer_iff.mp (dSp_mem_normalizer 1 μ) _),
    diagSL_mem_antiUnipotent_iff]

theorem diagSLμ_mem_normalizer (μ : kˣ) {g : SL(2, k)} (hg : g ∈ sl2Borel k) :
    diagSLμ μ g ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  rw [diagSLμ_apply]
  have hd := dSp_mem_normalizer (K := k) 1 μ
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd (diagSL_mem_normalizer hg))
    (Subgroup.inv_mem _ hd)

end CFSG.Quasithin.Ch3E213M.P6D
