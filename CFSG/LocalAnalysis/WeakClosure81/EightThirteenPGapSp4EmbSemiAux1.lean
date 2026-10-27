module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSl2Emb
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Tis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix

noncomputable section

variable {F : Type} [Field F] [CharP F 2]

def wcgapesM (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![g 0 0 ^ 2, 0; g 0 0 * g 1 0, 1]
    !![g 0 1 ^ 2, g 0 0 * g 0 1; g 0 1 * g 1 1, g 0 1 * g 1 0]
    !![g 1 0 ^ 2, 0; 0, 0]
    !![g 1 1 ^ 2, g 1 0 * g 1 1; 0, 1]

theorem wcgapesM_mul (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    wcgapesM g * wcgapesM h = wcgapesM (g * h) := by
  have hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two] at this
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wcgapesM, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.fromBlocks_multiply]
  all_goals
    first
      | linear_combination (g 0 0 * g 0 1) * hh +
          (g 0 0 * g 0 1 - g 0 0 * g 0 1 * h 0 0 * h 1 1) * h2
      | linear_combination (h 0 0 * h 1 0) * hg +
          (h 0 0 * h 1 0 - g 0 0 * g 1 1 * h 0 0 * h 1 0) * h2
      | linear_combination (h 0 1 * h 1 1) * hg +
          (h 0 1 * h 1 1 - g 0 0 * g 1 1 * h 0 1 * h 1 1) * h2
      | linear_combination (h 0 1 * h 1 0) * hg + (g 0 1 * g 1 0) * hh +
          (h 0 1 * h 1 0 + g 0 1 * g 1 0 + g 0 1 * g 1 0 * h 0 1 * h 1 0 -
            g 0 1 * g 1 0 * h 0 0 * h 1 1 - g 0 0 * g 1 1 * h 0 1 * h 1 0) * h2
      | linear_combination (g 1 0 * g 1 1) * hh +
          (g 1 0 * g 1 1 - g 1 0 * g 1 1 * h 0 0 * h 1 1) * h2
      | linear_combination (-(g 0 0 * g 0 1 * h 0 0 * h 1 0)) * h2
      | linear_combination (-(g 0 0 * g 0 1 * h 0 1 * h 1 1)) * h2
      | linear_combination (-(g 1 0 * g 1 1 * h 0 0 * h 1 0)) * h2
      | linear_combination (-(g 1 0 * g 1 1 * h 0 1 * h 1 1)) * h2
      | ring

theorem wcgapesM_one : wcgapesM (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wcgapesM, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

theorem wcgapesM_symp (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (wcgapesM g)ᵀ * fromBlocks 0 1 (-1) 0 * wcgapesM g = fromBlocks 0 1 (-1) 0 := by
  have hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wcgapesM, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks_multiply, Matrix.transpose_apply]
  all_goals
    first
      | linear_combination (1 + g 0 1 * g 1 0 + g 0 0 * g 1 1) * hg + (g 0 1 * g 1 0) * h2
      | linear_combination (g 0 0 * g 1 0) * hg + (g 0 0 * g 1 0) * h2
      | linear_combination (1 + g 0 1 * g 1 0 + g 0 0 * g 1 1) * hg +
          (1 + g 0 1 * g 1 0 + g 0 1 ^ 2 * g 1 0 ^ 2 - g 0 0 ^ 2 * g 1 1 ^ 2) * h2
      | linear_combination (g 0 1 * g 1 1) * hg +
          (g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0 * g 1 1 - g 0 0 * g 0 1 * g 1 1 ^ 2) * h2
      | linear_combination (g 0 0 * g 1 0) * hg +
          (g 0 0 * g 0 1 * g 1 0 ^ 2 - g 0 0 ^ 2 * g 1 0 * g 1 1) * h2
      | linear_combination (g 0 1 * g 1 1) * hg + (0 : F) * h2
      | ring

def wcgapesGL (g : Matrix.SpecialLinearGroup (Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F :=
  Units.mk (wcgapesM g) (wcgapesM g⁻¹)
    (by rw [wcgapesM_mul, mul_inv_cancel, wcgapesM_one])
    (by rw [wcgapesM_mul, inv_mul_cancel, wcgapesM_one])

@[expose]
def wcgapesIota1 (g : Matrix.SpecialLinearGroup (Fin 2) F) : StatedSp 2 F :=
  ⟨wcgapesGL g, by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup]
    exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mp
      (wcgapesM_symp g)⟩

@[simp]
theorem wcgapesIota1_coe (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((wcgapesIota1 g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = wcgapesM g := by
  simp [wcgapesIota1, wcgapesGL, Units.val_mk]

theorem wcgapesIota1_mul (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    wcgapesIota1 (g * h) = wcgapesIota1 g * wcgapesIota1 h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, wcgapesIota1_coe, ← wcgapesM_mul]

theorem wcgapesIota1_one :
    wcgapesIota1 (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_one, Units.val_one, wcgapesIota1_coe, wcgapesM_one]

@[expose]
def wcgapesIota1Hom : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 2 F where
  toFun := wcgapesIota1
  map_one' := wcgapesIota1_one
  map_mul' := wcgapesIota1_mul

def wcgapesUnitriSL (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

theorem wcgapes_sq_injective [Finite F] (hF : Nat.card F = 4) (x y : F) (h : x ^ 2 = y ^ 2) :
    x = y := by
  letI := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have pow4 : ∀ z : F, z ^ 4 = z := by
    intro z
    have hz := FiniteField.pow_card (K := F) z
    rwa [hcard] at hz
  calc x = x ^ 4 := (pow4 x).symm
    _ = (x ^ 2) ^ 2 := by ring
    _ = (y ^ 2) ^ 2 := by rw [h]
    _ = y ^ 4 := by ring
    _ = y := pow4 y

theorem wcgapesIota1_injective [Finite F] (hF : Nat.card F = 4) :
    Function.Injective (wcgapesIota1 (F := F)) := by
  intro g h hgh
  have hgh' : wcgapesM g = wcgapesM h := by
    have := congrArg (fun x : StatedSp 2 F =>
      (((x : GL (Fin 2 ⊕ Fin 2) F)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hgh
    rwa [wcgapesIota1_coe, wcgapesIota1_coe] at this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · have hsq : (g 0 0) ^ 2 = (h 0 0) ^ 2 := by
      have := congrFun (congrFun hgh' (Sum.inl 0)) (Sum.inl 0)
      simpa [wcgapesM, fromBlocks_apply₁₁] using this
    exact wcgapes_sq_injective hF _ _ hsq
  · have hsq : (g 0 1) ^ 2 = (h 0 1) ^ 2 := by
      have := congrFun (congrFun hgh' (Sum.inl 0)) (Sum.inr 0)
      simpa [wcgapesM, fromBlocks_apply₁₂] using this
    exact wcgapes_sq_injective hF _ _ hsq
  · have hsq : (g 1 0) ^ 2 = (h 1 0) ^ 2 := by
      have := congrFun (congrFun hgh' (Sum.inr 0)) (Sum.inl 0)
      simpa [wcgapesM, fromBlocks_apply₂₁] using this
    exact wcgapes_sq_injective hF _ _ hsq
  · have hsq : (g 1 1) ^ 2 = (h 1 1) ^ 2 := by
      have := congrFun (congrFun hgh' (Sum.inr 0)) (Sum.inr 0)
      simpa [wcgapesM, fromBlocks_apply₂₂] using this
    exact wcgapes_sq_injective hF _ _ hsq

theorem wcgapesIota1_unitri (t : F) :
    wcgapesIota1 (wcgapesUnitriSL t) = sp4Z (t ^ 2) t := by
  apply Subtype.ext
  apply Units.ext
  rw [wcgapesIota1_coe, sp4Z, coe_tau]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [wcgapesM, wcgapesUnitriSL, sym2]

theorem wcgapesM_diag (l : Fˣ) :
    wcgapesM (slTwoDiag l) = blockMat !![(l : F) ^ 2, 0; 0, 1] 0 := by
  have hinv : (!![(l : F) ^ 2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F)⁻¹ =
      !![((l : F) ^ 2)⁻¹, 0; 0, 1] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀]
  rw [blockMat, Matrix.mul_zero, hinv]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [wcgapesM, slTwoDiag, inv_pow, Matrix.transpose_apply]

theorem wcgapes_pow_four [Finite F] (hF : Nat.card F = 4) (x : F) : x ^ 4 = x := by
  letI := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hz := FiniteField.pow_card (K := F) x
  rwa [hcard] at hz

theorem wcgapesUnitriSL_mem (t : F) : wcgapesUnitriSL t ∈ unitriangular 2 F := by
  rw [mem_unitriangular]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [wcgapesUnitriSL]
  · intro i
    fin_cases i <;> simp [wcgapesUnitriSL]

theorem wcgapes_mem_map_unitriangular [Finite F] (hF : Nat.card F = 4) (g : StatedSp 2 F) :
    g ∈ (unitriangular 2 F).map wcgapesIota1Hom ↔ ∃ s : F, g = sp4Z s (s ^ 2) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : F, u = wcgapesUnitriSL t := by
      refine ⟨u 0 1, ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp_all [mem_unitriangular, wcgapesUnitriSL]
    refine ⟨t ^ 2, ?_⟩
    change wcgapesIota1 u = sp4Z (t ^ 2) ((t ^ 2) ^ 2)
    rw [ht, wcgapesIota1_unitri,
      show (t ^ 2) ^ 2 = t by rw [← pow_mul]; norm_num; exact wcgapes_pow_four hF t]
  · rintro ⟨s, rfl⟩
    refine ⟨wcgapesUnitriSL (s ^ 2), wcgapesUnitriSL_mem _, ?_⟩
    change wcgapesIota1 (wcgapesUnitriSL (s ^ 2)) = sp4Z s (s ^ 2)
    rw [wcgapesIota1_unitri,
      show (s ^ 2) ^ 2 = s by rw [← pow_mul]; norm_num; exact wcgapes_pow_four hF s]

def wcgapesHb (b : F) (hb : b ≠ 0) : StatedSp 2 F :=
  torusHom ![1, Units.mk0 b hb]

theorem wcgapesHb_coe (b : F) (hb : b ≠ 0) :
    (((wcgapesHb b hb : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks !![1, 0; 0, b] 0 0 !![1, 0; 0, b⁻¹] := by
  rw [wcgapesHb, coe_torusHom, ← Matrix.fromBlocks_diagonal]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Units.val_inv_eq_inv_val]

theorem wcgapesHb_inv_coe (b : F) (hb : b ≠ 0) :
    ((((wcgapesHb b hb)⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks !![1, 0; 0, b⁻¹] 0 0 !![1, 0; 0, b] := by
  rw [wcgapesHb, ← map_inv, coe_torusHom, ← Matrix.fromBlocks_diagonal]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Units.val_inv_eq_inv_val]

theorem wcgapes_conj_sp4Z (b : F) (hb : b ≠ 0) (s : F) :
    wcgapesHb b hb * sp4Z s (s ^ 2) * (wcgapesHb b hb)⁻¹ = sp4Z s (b * s ^ 2) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    wcgapesHb_coe, wcgapesHb_inv_coe, sp4Z, coe_tau, sp4Z, coe_tau]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sym2, hb, inv_mul_cancel₀, mul_inv_cancel₀,
      mul_comm]


theorem wcgapesHb_coe_blockMat (b : F) (hb : b ≠ 0) :
    (((wcgapesHb b hb : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = blockMat !![1, 0; 0, b] 0 := by
  have hinv : (!![1, 0; 0, b] : Matrix (Fin 2) (Fin 2) F)⁻¹ = !![1, 0; 0, b⁻¹] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb, inv_mul_cancel₀, mul_inv_cancel₀]
  rw [wcgapesHb_coe, blockMat, Matrix.mul_zero, hinv]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply]


end

end CFSG.LocalAnalysis.WeakClosure81

end
