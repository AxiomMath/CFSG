module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Faithful
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Onto

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

variable {K : Type} [Field K]

theorem f4B2Rep_torus_onto
    {A : GL (Fin 4) K} (hA : A ∈ matrixIsometryGroup (f4J0 K))
    {d : Fin 4 → K} (hd : (A : Matrix (Fin 4) (Fin 4) K) = diagonal d) :
    ∃ t u : Kˣ, (((f4B2Rep K ⟨torusElt Tag.F4 K 1 t * torusElt Tag.F4 K 2 u,
      torusElt_pair_mem 1 2 t u⟩ : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = A := by
  have h := (mem_matrixIsometryGroup.1 hA)
  rw [hd] at h
  have e := fun p q => congrFun (congrFun h p) q
  have e03 := e 0 3
  have e12 := e 1 2
  simp [f4J0, Matrix.mul_apply, Matrix.diagonal_apply] at e03 e12
  have hd0 : d 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at e03; exact zero_ne_one e03
  have hd1 : d 1 ≠ 0 := fun h1 => by rw [h1, zero_mul] at e12; exact zero_ne_one e12
  refine ⟨Units.mk0 (d 0) hd0 * Units.mk0 (d 1) hd1, Units.mk0 (d 0) hd0, ?_⟩
  rw [f4B2Rep_torus, hd]
  congr 1
  funext k
  fin_cases k <;> simp <;> field_simp <;>
    first
    | linear_combination e12
    | linear_combination -e12
    | linear_combination e03
    | linear_combination -e03

theorem f4B2_diag_x1 (a b c : K) :
    diagonal ![a * b ^ 2, a * b, b, 1] * (1 + single 1 2 c : Matrix (Fin 4) (Fin 4) K) =
      (1 + single 1 2 (a * c)) * diagonal ![a * b ^ 2, a * b, b, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  ring

theorem f4B2_diag_y1 {a b : K} (ha : a ≠ 0) (c : K) :
    diagonal ![a * b ^ 2, a * b, b, 1] * (1 + single 2 1 c : Matrix (Fin 4) (Fin 4) K) =
      (1 + single 2 1 (a⁻¹ * c)) * diagonal ![a * b ^ 2, a * b, b, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  field_simp

theorem f4B2_diag_x2 (a b c : K) :
    diagonal ![a * b ^ 2, a * b, b, 1] *
        (1 + single 0 1 c + single 2 3 c : Matrix (Fin 4) (Fin 4) K) =
      (1 + single 0 1 (b * c) + single 2 3 (b * c)) * diagonal ![a * b ^ 2, a * b, b, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  ring

theorem f4B2_diag_y2 {a b : K} (hb : b ≠ 0) (c : K) :
    diagonal ![a * b ^ 2, a * b, b, 1] *
        (1 + single 1 0 c + single 3 2 c : Matrix (Fin 4) (Fin 4) K) =
      (1 + single 1 0 (b⁻¹ * c) + single 3 2 (b⁻¹ * c)) * diagonal ![a * b ^ 2, a * b, b, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    field_simp

theorem f4B2_conj
    {h : ModGL Tag.F4 K} (hh : h ∈ torusGroup Tag.F4 K) {a b : K}
    (ha : (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single 1 1)) =
      a • rootVec Tag.F4 K (Pi.single 1 1))
    (hb : (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single 2 1)) =
      b • rootVec Tag.F4 K (Pi.single 2 1))
    (g : ModGL Tag.F4 K) (hg : g ∈ subsystemGroup Tag.F4 K {1, 2}) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.F4 K {1, 2} ∧
      diagonal ![a * b ^ 2, a * b, b, 1] * blockMat f4B2Weight g =
        blockMat f4B2Weight (h * g * h⁻¹) * diagonal ![a * b ^ 2, a * b, b, 1] := by
  obtain ⟨ha0, hxa, hya⟩ := conj_xUnit_of_apply_single hh ha
  obtain ⟨hb0, hxb, hyb⟩ := conj_xUnit_of_apply_single hh hb
  have hl := left_mem_pair (1 : Fin Tag.F4.rank) 2
  have hr := right_mem_pair (1 : Fin Tag.F4.rank) 2
  have hB := isSliceBlock_f4B2Weight
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · rcases (show k = 1 ∨ k = 2 from hk) with rfl | rfl
      · rw [hxa]
        exact ⟨xUnit_mem_subsystemGroup hl _, by
          rw [f4B2BlockMat_x1, f4B2BlockMat_x1, f4B2_diag_x1]⟩
      · rw [hxb]
        exact ⟨xUnit_mem_subsystemGroup hr _, by
          rw [f4B2BlockMat_x2, f4B2BlockMat_x2, f4B2_diag_x2]⟩
    · rcases (show k = 1 ∨ k = 2 from hk) with rfl | rfl
      · rw [hya]
        exact ⟨yUnit_mem_subsystemGroup hl _, by
          rw [f4B2BlockMat_y1, f4B2BlockMat_y1, f4B2_diag_y1 ha0]⟩
      · rw [hyb]
        exact ⟨yUnit_mem_subsystemGroup hr _, by
          rw [f4B2BlockMat_y2, f4B2BlockMat_y2, f4B2_diag_y2 hb0]⟩
  | one =>
    rw [mul_one, mul_inv_cancel, hB.blockMat_one', Matrix.mul_one, Matrix.one_mul]
    exact ⟨one_mem _, rfl⟩
  | mul x y _ hy ihx ihy =>
    rw [show h * (x * y) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) by group]
    refine ⟨mul_mem ihx.1 ihy.1, ?_⟩
    rw [hB.blockMat_mul' hy, hB.blockMat_mul' ihy.1, ← Matrix.mul_assoc, ihx.2, Matrix.mul_assoc,
      ihy.2, Matrix.mul_assoc]
  | inv x hx ihx =>
    rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
    refine ⟨inv_mem ihx.1, ?_⟩
    have h1 : blockMat f4B2Weight x * blockMat f4B2Weight x⁻¹ = 1 := by
      rw [← hB.blockMat_mul' (inv_mem hx), mul_inv_cancel, hB.blockMat_one']
    have h2 : blockMat f4B2Weight (h * x * h⁻¹)⁻¹ * blockMat f4B2Weight (h * x * h⁻¹) = 1 := by
      rw [← hB.blockMat_mul' ihx.1, inv_mul_cancel, hB.blockMat_one']
    calc diagonal ![a * b ^ 2, a * b, b, 1] * blockMat f4B2Weight x⁻¹ =
        blockMat f4B2Weight (h * x * h⁻¹)⁻¹ * blockMat f4B2Weight (h * x * h⁻¹) *
          (diagonal ![a * b ^ 2, a * b, b, 1] * blockMat f4B2Weight x⁻¹) := by
          rw [h2, Matrix.one_mul]
      _ = blockMat f4B2Weight (h * x * h⁻¹)⁻¹ *
          (diagonal ![a * b ^ 2, a * b, b, 1] * blockMat f4B2Weight x) *
            blockMat f4B2Weight x⁻¹ := by
          rw [ihx.2]
          simp only [Matrix.mul_assoc]
      _ = blockMat f4B2Weight (h * x * h⁻¹)⁻¹ * diagonal ![a * b ^ 2, a * b, b, 1] := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem f4B2_similitude (a b : K) :
    (diagonal ![a * b ^ 2, a * b, b, 1])ᵀ * f4J0 K * diagonal ![a * b ^ 2, a * b, b, 1] =
      (a * b ^ 2) • f4J0 K := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [f4J0, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem F4_native_B2_faithful_Sp4_all_characteristics
    (K : Type) [Field K] :
    (∀ g ∈ subsystemGroup Tag.F4 K {1, 2}, ∀ m ∈ blockSpan K f4B2Weight,
      (g : Module.End K (RootModule Tag.F4 K)) m ∈ blockSpan K f4B2Weight) ∧
    (∀ (g : subsystemGroup Tag.F4 K {1, 2}) (j : Fin 4),
      ((g : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))
          (rootVec Tag.F4 K (f4B2Weight j)) =
        ∑ i, (((f4B2Rep K g : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) i j • rootVec Tag.F4 K (f4B2Weight i)) ∧
    Function.Bijective (f4B2Rep K) ∧
    (∀ c : K,
      (((f4B2Rep K (qx (left_mem_pair 1 2) c) : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + single 1 2 c ∧
      (((f4B2Rep K (qy (left_mem_pair 1 2) c) : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + single 2 1 c ∧
      (((f4B2Rep K (qx (right_mem_pair 1 2) c) : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + single 0 1 c + single 2 3 c ∧
      (((f4B2Rep K (qy (right_mem_pair 1 2) c) : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + single 1 0 c + single 3 2 c) ∧
    (∀ t u : Kˣ,
      (((f4B2Rep K ⟨torusElt Tag.F4 K 1 t * torusElt Tag.F4 K 2 u, torusElt_pair_mem 1 2 t u⟩ :
        matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal ![(u : K), (t : K) * (u : K)⁻¹, (t : K)⁻¹ * u, (u : K)⁻¹]) ∧
    (∀ A ∈ matrixIsometryGroup (f4J0 K), ∀ d : Fin 4 → K,
      (A : Matrix (Fin 4) (Fin 4) K) = diagonal d →
      ∃ t u : Kˣ, (((f4B2Rep K ⟨torusElt Tag.F4 K 1 t * torusElt Tag.F4 K 2 u,
        torusElt_pair_mem 1 2 t u⟩ : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) = A) ∧
    subsystemGroup Tag.F4 K {1, 2} = rootSpan Tag.F4 K (parabolicRoots Tag.F4 {1, 2}) ∧
    (∀ g : ModGL Tag.F4 K, g ∈ subsystemGroup Tag.F4 K {1, 2} ⊓ torusGroup Tag.F4 K ↔
      ∃ t u : Kˣ, g = torusElt Tag.F4 K 1 t * torusElt Tag.F4 K 2 u) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : subsystemGroup Tag.F4 K {1, 2}),
      ∃ hσ : baseChangeGL σ (g : ModGL Tag.F4 K) ∈ subsystemGroup Tag.F4 L {1, 2},
        (((f4B2Rep L ⟨_, hσ⟩ : matrixIsometryGroup (f4J0 L)) : GL (Fin 4) L) :
          Matrix (Fin 4) (Fin 4) L) =
        (((f4B2Rep K g : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K).map σ) ∧
    (∀ h ∈ torusGroup Tag.F4 K, ∀ a b : K,
      (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single 1 1)) =
        a • rootVec Tag.F4 K (Pi.single 1 1) →
      (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single 2 1)) =
        b • rootVec Tag.F4 K (Pi.single 2 1) →
      (∃ hN : ∀ z ∈ subsystemGroup Tag.F4 K {1, 2}, h * z * h⁻¹ ∈ subsystemGroup Tag.F4 K {1, 2},
        ∀ z : subsystemGroup Tag.F4 K {1, 2},
          (((f4B2Rep K ⟨h * z * h⁻¹, hN z z.2⟩ : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K) =
          diagonal ![a * b ^ 2, a * b, b, 1] *
            (((f4B2Rep K z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
              Matrix (Fin 4) (Fin 4) K) * (diagonal ![a * b ^ 2, a * b, b, 1])⁻¹) ∧
      (diagonal ![a * b ^ 2, a * b, b, 1])ᵀ * f4J0 K * diagonal ![a * b ^ 2, a * b, b, 1] =
        (a * b ^ 2) • f4J0 K) ∧
    ∃ z : subsystemGroup Tag.F4 K {1, 2},
      (((f4B2Rep K z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = -1 := by
  refine ⟨fun g hg m hm => isSliceBlock_f4B2Weight.mem_blockSpan hg hm, fun g j => ?_,
    ⟨f4B2Rep_injective, f4B2Rep_surjective⟩, fun c => ⟨f4B2BlockMat_x1 c, f4B2BlockMat_y1 c,
      f4B2BlockMat_x2 c, f4B2BlockMat_y2 c⟩, f4B2Rep_torus,
    fun A hA d hd => f4B2Rep_torus_onto hA hd, subsystemGroup_eq_rootSpan _,
    fun g => ?_, fun L _ σ g => ⟨baseChangeGL_mem_subsystemGroup σ g.2, ?_⟩,
    fun h hh a b ha hb => ⟨⟨fun z hz => (f4B2_conj hh ha hb z hz).1, fun z => ?_⟩,
      f4B2_similitude a b⟩, ?_⟩
  · rw [coe_f4B2Rep]
    exact apply_rootVec_eq_sum isSliceBlock_f4B2Weight.isRoot isSliceBlock_f4B2Weight.injective
      (fun _ hm => isSliceBlock_f4B2Weight.mem_blockSpan g.2 hm) j
  · rw [subsystemGroup_inf_torusGroup, mem_subsystemTorus_pair]
  · rw [coe_f4B2Rep, coe_f4B2Rep]
    exact blockMat_baseChangeGL σ isSliceBlock_f4B2Weight.isRoot _
  · obtain ⟨ha0, -, -⟩ := conj_xUnit_of_apply_single hh ha
    obtain ⟨hb0, -, -⟩ := conj_xUnit_of_apply_single hh hb
    have hD := (f4B2_conj hh ha hb z z.2).2
    have hdet : IsUnit (diagonal ![a * b ^ 2, a * b, b, 1]).det := by
      rw [Matrix.det_diagonal, Fin.prod_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one]
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero 2 hb0)) (mul_ne_zero ha0 hb0))
        hb0).isUnit
    rw [coe_f4B2Rep, coe_f4B2Rep, hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      Matrix.mul_one]
  · have hm : (-1 : GL (Fin 4) K) ∈ matrixIsometryGroup (f4J0 K) := by
      rw [mem_matrixIsometryGroup, Units.val_neg, Units.val_one, Matrix.transpose_neg,
        Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one,
        neg_neg]
    obtain ⟨z, hz⟩ := f4B2Rep_surjective (K := K) ⟨-1, hm⟩
    exact ⟨z, by rw [hz]; rfl⟩

end CFSG.RankThree.Chevalley
