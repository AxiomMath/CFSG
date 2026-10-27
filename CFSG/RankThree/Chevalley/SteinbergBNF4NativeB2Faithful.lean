module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Rep

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open scoped Pointwise

variable {K : Type} [Field K]

theorem f4B2_weyl1 :
    (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) K) * (1 + single 2 1 (-1)) * (1 + single 1 2 1) =
      !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem f4B2_weyl1_inv :
    (1 + single 1 2 (-1) : Matrix (Fin 4) (Fin 4) K) * (1 + single 2 1 1) * (1 + single 1 2 (-1)) =
      !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem f4B2_weyl2 :
    (1 + single 0 1 1 + single 2 3 1 : Matrix (Fin 4) (Fin 4) K) *
        (1 + single 1 0 (-1) + single 3 2 (-1)) * (1 + single 0 1 1 + single 2 3 1) =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem f4B2_weyl2_inv :
    (1 + single 0 1 (-1) + single 2 3 (-1) : Matrix (Fin 4) (Fin 4) K) *
        (1 + single 1 0 1 + single 3 2 1) * (1 + single 0 1 (-1) + single 2 3 (-1)) =
      !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem f4B2_conj1 (c : K) :
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1] *
        (1 + single 0 1 c + single 2 3 c : Matrix (Fin 4) (Fin 4) K) *
        !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1] =
      1 + single 0 2 (-c) + single 1 3 c := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct, Matrix.one_apply]

theorem f4B2_conj2 (c : K) :
    !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] *
        (1 + single 1 2 c : Matrix (Fin 4) (Fin 4) K) *
        !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0] =
      1 + single 0 3 (-c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct, Matrix.one_apply]

theorem range_f4B2Pos
    : Set.range f4B2Pos = parabolicPosRoots Tag.F4 {1, 2} := by
  obtain ⟨hroot, hout, hall, -⟩ := f4B2Pos_checks
  ext α
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := hroot a
    have hα : IsRoot Tag.F4 (f4B2Pos a) := isRoot_F4_iff.2 ⟨k, hk⟩
    refine ⟨⟨hα, fun s hs => ?_⟩, hα, (hout a).2.2⟩
    have h03 : s = 0 ∨ s = 3 := by
      have hs' : ¬(s = 1 ∨ s = 2) := hs
      revert s
      decide
    rcases h03 with rfl | rfl
    · exact (hout a).1
    · exact (hout a).2.1
  · rintro ⟨⟨hα, hz⟩, -, hpos⟩
    obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hα
    refine hall k (hz 0 ?_) (hz 3 ?_) hpos
    · rintro (h | h) <;> exact absurd h (by decide)
    · rintro (h | h) <;> exact absurd h (by decide)

theorem f4B2Rep_injective
    : Function.Injective (f4B2Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : blockMat f4B2Weight (g : ModGL Tag.F4 K) = 1 := by
    rw [← coe_f4B2Rep, hg]
    rfl
  have hb : (g : ModGL Tag.F4 K) ∈ (subsystemTorus Tag.F4 K {1, 2} : Set (ModGL Tag.F4 K)) *
      (parabolicLeviUnipotent Tag.F4 K {1, 2} : Set (ModGL Tag.F4 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.F4) (K := K) (A := {1, 2})) _).mp
      (isSliceBlock_f4B2Weight.mem_subsystemBorel g.2 hmat)
  obtain ⟨t', ht', u', hu', htu⟩ := hb
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_pair.1 ht'
  obtain ⟨-, -, -, hinj, h0, h1, h2, h3⟩ := f4B2Pos_checks
  obtain ⟨x, -, rfl⟩ :=
    (bijOn_prod_pinnedX_parabolicPosRoots (K := K) f4B2Pos hinj range_f4B2Pos).surjOn hu'
  obtain ⟨ε, hε, hconj⟩ := weylElt_mul_pinnedX_mul_inv K 1 (isRoot_single Tag.F4 2)
  obtain ⟨ε', hε', hconj'⟩ := weylElt_mul_pinnedX_mul_inv K 2 (isRoot_single Tag.F4 1)
  have hl := left_mem_pair (1 : Fin Tag.F4.rank) 2
  have hr := right_mem_pair (1 : Fin Tag.F4.rank) 2
  set N₁ : subsystemGroup Tag.F4 K {1, 2} := ⟨weylElt Tag.F4 K 1 1, weylElt_mem_subsystemGroup hl 1⟩
    with hN₁
  set N₂ : subsystemGroup Tag.F4 K {1, 2} := ⟨weylElt Tag.F4 K 2 1, weylElt_mem_subsystemGroup hr 1⟩
    with hN₂
  have hN₁e : N₁ = qx hl 1 * qy hl (-1) * qx hl 1 := weylElt_one_eq_prod hl
  have hN₂e : N₂ = qx hr 1 * qy hr (-1) * qx hr 1 := weylElt_one_eq_prod hr
  have hN₁i : N₁⁻¹ = qx hl (-1) * qy hl 1 * qx hl (-1) := by
    rw [hN₁e, _root_.mul_inv_rev, _root_.mul_inv_rev, qx_inv, qy_inv, neg_neg, mul_assoc]
  have hN₂i : N₂⁻¹ = qx hr (-1) * qy hr 1 * qx hr (-1) := by
    rw [hN₂e, _root_.mul_inv_rev, _root_.mul_inv_rev, qx_inv, qy_inv, neg_neg, mul_assoc]
  have hX2 : pinnedX Tag.F4 K (f4B2Pos 2) (x 2) =
      weylElt Tag.F4 K 1 1 * xUnit Tag.F4 K 2 (ε * x 2) * (weylElt Tag.F4 K 1 1)⁻¹ := by
    have e := hconj (ε * x 2)
    rw [pinnedX_single, ← mul_assoc, hε, one_mul] at e
    rw [h2, ← e]
  have hX3 : pinnedX Tag.F4 K (f4B2Pos 3) (x 3) =
      weylElt Tag.F4 K 2 1 * xUnit Tag.F4 K 1 (ε' * x 3) * (weylElt Tag.F4 K 2 1)⁻¹ := by
    have e := hconj' (ε' * x 3)
    rw [pinnedX_single, ← mul_assoc, hε', one_mul] at e
    rw [h3, ← e]
  have hgprod : g = ⟨torusElt Tag.F4 K 1 a * torusElt Tag.F4 K 2 b, torusElt_pair_mem 1 2 a b⟩ *
      (qx hr (x 0) * (qx hl (x 1) * (N₁ * qx hr (ε * x 2) * N₁⁻¹ *
        (N₂ * qx hl (ε' * x 3) * N₂⁻¹)))) := by
    apply Subtype.ext
    rw [← htu]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_qx, hN₁, hN₂]
    have e3 : (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) : Fin 4) = 3 := rfl
    have e2 : (Fin.succ (Fin.succ (0 : Fin 2)) : Fin 4) = 2 := rfl
    have e1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
    rw [e3, e2, e1, hX2, hX3, h0, h1, pinnedX_single, pinnedX_single]
  have hM := congrArg
    (fun A : matrixIsometryGroup (f4J0 K) => ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hg
  simp only [hgprod, map_mul, Subgroup.coe_mul, Units.val_mul] at hM
  rw [f4B2Rep_torus, hN₁i, hN₁e, hN₂i, hN₂e] at hM
  simp only [map_mul, Subgroup.coe_mul, Units.val_mul, coe_f4B2Rep, coe_qx, coe_qy,
    f4B2BlockMat_x1, f4B2BlockMat_y1, f4B2BlockMat_x2, f4B2BlockMat_y2] at hM
  rw [f4B2_weyl1, f4B2_weyl1_inv, f4B2_weyl2, f4B2_weyl2_inv, f4B2_conj1, f4B2_conj2] at hM
  have e := fun p q => congrFun (congrFun hM p) q
  have e00 := e 0 0
  have e11 := e 1 1
  have e01 := e 0 1
  have e12 := e 1 2
  have e02 := e 0 2
  have e03 := e 0 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply,
    Matrix.diagonal_apply] at e00 e11 e01 e12 e02 e03
  subst e00
  have ha : a = 1 := Units.ext (by simpa using e11)
  subst ha
  have hε0 : ε ≠ 0 := fun h => by
    rw [h, zero_mul] at hε
    exact zero_ne_one hε
  have hε'0 : ε' ≠ 0 := fun h => by
    rw [h, zero_mul] at hε'
    exact zero_ne_one hε'
  have hx2 : x 2 = 0 := by
    rw [e01, zero_mul, add_zero, neg_eq_zero] at e02
    exact (mul_eq_zero.1 e02).resolve_left hε0
  have hx3 : x 3 = 0 := by
    rw [e01, zero_mul, add_zero, neg_eq_zero] at e03
    exact (mul_eq_zero.1 e03).resolve_left hε'0
  have hx : x = 0 := by
    funext m
    fin_cases m
    exacts [e01, e12, hx2, hx3]
  subst hx
  apply Subtype.ext
  rw [← htu]
  simp [torusElt_one, pinnedX_zero]

end CFSG.RankThree.Chevalley.SteinbergBN
