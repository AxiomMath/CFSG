module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalPlane
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSpan
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.Open.PGLModelStated
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open CFSG.LieType.BorelTits CFSG.Theory.Representation
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped commutatorElement

@[expose] def suPlaneOrder : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
  finSumFinEquiv

variable {K : Type} [Field K]

theorem exists_sq_add_zero_sq_eq_neg_one (hK : Nat.card K = 9) : ∃ i : K, i ^ 2 + 0 ^ 2 = -1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨i, hi⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by rw [hcard]; norm_num)
  exact ⟨i, by rw [hi]; ring⟩

@[expose] noncomputable def suP0 {i : K} (h : i ^ 2 + 0 ^ 2 = -1) : Subgroup (GL (Fin 4) K) :=
  (planeP0 h).map (suPlaneOrder.reindexGL K).toMonoidHom

private theorem ringChar_ne_two_of_card_eq_nine (hK : Nat.card K = 9) : ringChar K ≠ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card K (ringChar K)
  have h9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [h9] at hcard
  have hpow : ringChar K ^ (n : ℕ) = 3 ^ 2 := by rw [← hcard]; norm_num
  have hdvd : ringChar K ∣ 3 ^ 2 := by
    rw [← hpow]
    exact dvd_pow_self _ n.pos.ne'
  have hdvd3 : ringChar K ∣ 3 := hprime.dvd_of_dvd_pow hdvd
  have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).1 hdvd3
  omega

private theorem quatHom_cube_transpose_mul {i : K} (h : i ^ 2 + 0 ^ 2 = -1)
    (q : QuaternionGroup 2) :
    (((quatHom h q : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h q : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  have hi2 : i ^ 2 = -1 := by linear_combination h
  have hi3 : i ^ 3 = -i := by rw [pow_succ, hi2]; ring
  have hi2' : i * i = -1 := by rw [← sq, hi2]
  have hni3 : (-i) ^ 3 = i := by rw [neg_pow, hi3]; ring
  have hneg3 : ((-1 : K) ^ 3) = -1 := by norm_num
  have hmapneg : ((-1 : Matrix (Fin 2) (Fin 2) K).map (· ^ 3)) = -1 := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [hneg3]
  rcases q with k | k <;> fin_cases k
  · change (((quatHom h (.a 0) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.a 0) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_a_zero h]; simp
  · change (((quatHom h (.a 1) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.a 1) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_a_one h]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [quatI, hneg3, Matrix.mul_apply, Fin.sum_univ_two]
  · change (((quatHom h (.a 2) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.a 2) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_a_two h, hmapneg]; simp
  · change (((quatHom h (.a 3) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.a 3) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_a_three h]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [quatI, hneg3, Matrix.mul_apply, Fin.sum_univ_two]
  · change (((quatHom h (.xa 0) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.xa 0) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_xa_zero h]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [quatJ, hi2', hi3, hni3, Matrix.mul_apply, Fin.sum_univ_two]
  · change (((quatHom h (.xa 1) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.xa 1) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_xa_one h, quatI_mul_quatJ]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [hi2', hi3, Matrix.mul_apply, Fin.sum_univ_two]
  · change (((quatHom h (.xa 2) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.xa 2) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_xa_two h]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [quatJ, hi2', hi3, hni3, Matrix.mul_apply, Fin.sum_univ_two]
  · change (((quatHom h (.xa 3) : Matrix (Fin 2) (Fin 2) K).map (· ^ 3))ᵀ *
      (quatHom h (.xa 3) : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [quatHom_xa_three h, quatI_mul_quatJ]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [hi2', hni3, Matrix.mul_apply, Fin.sum_univ_two]

private theorem planeQuat_det_matrix {i : K} (h : i ^ 2 + 0 ^ 2 = -1)
    (x : QuaternionGroup 2 × QuaternionGroup 2) :
    ((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 := by
  rw [coe_planeQuat, Matrix.det_fromBlocks_zero₂₁, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe, one_mul]

private theorem planeQuat_unitary {i : K} (h : i ^ 2 + 0 ^ 2 = -1)
    (x : QuaternionGroup 2 × QuaternionGroup 2) :
    ((((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (· ^ 3))ᵀ *
      ((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 1 := by
  rw [coe_planeQuat, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  rw [quatHom_cube_transpose_mul h x.1, quatHom_cube_transpose_mul h x.2]
  simp [Matrix.fromBlocks_one]

private theorem suPairSwap_inl_zero :
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Sum.inl 0) = Sum.inl 0 := by decide
private theorem suPairSwap_inl_one :
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Sum.inl 1) = Sum.inr 0 := by decide
private theorem suPairSwap_inr_zero :
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Sum.inr 0) = Sum.inl 1 := by decide
private theorem suPairSwap_inr_one :
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Sum.inr 1) = Sum.inr 1 := by decide

private theorem planeSwap_det_matrix :
    ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 := by
  rw [coe_planeSwap]
  have hB : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = -1 := by
    rw [Matrix.det_fin_two]
    norm_num
  have hD : (fromBlocks (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_fromBlocks_zero₂₁, hB]
    norm_num
  have hS : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (fromBlocks (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)).submatrix
        (Equiv.swap (Sum.inl 1) (Sum.inr 0)).symm
        (Equiv.swap (Sum.inl 1) (Sum.inr 0)).symm := by
    rw [Equiv.symm_swap]
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j
    all_goals
      simp only [Matrix.submatrix_apply]
      repeat' first
        | rw [Matrix.fromBlocks_apply₁₁]
        | rw [Matrix.fromBlocks_apply₁₂]
        | rw [Matrix.fromBlocks_apply₂₁]
        | rw [Matrix.fromBlocks_apply₂₂]
        | rw [suPairSwap_inl_zero]
        | rw [suPairSwap_inl_one]
        | rw [suPairSwap_inr_zero]
        | rw [suPairSwap_inr_one]
      rfl
  rw [hS, Matrix.det_submatrix_equiv_self _, hD]

private theorem planeSwap_unitary :
    (((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (· ^ 3))ᵀ *
      ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  rw [coe_planeSwap, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  rw [show (0 : Matrix (Fin 2) (Fin 2) K).map (· ^ 3) = 0 by
    rw [Matrix.map_zero]; norm_num]
  simp [Matrix.fromBlocks_one]

theorem suP0_le_statedSU {i : K} (h : i ^ 2 + 0 ^ 2 = -1) : suP0 h ≤ StatedSU 4 3 K := by
  rw [CFSG.PGLModel.statedSU_eq_closure_det, suP0, Subgroup.map_le_iff_le_comap,
    planeP0, sup_le_iff]
  constructor
  · rintro _ ⟨x, rfl⟩
    apply Subgroup.subset_closure
    have hcoe : (((suPlaneOrder.reindexGL K).toMonoidHom (planeQuat h x) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      ((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix
          suPlaneOrder.symm suPlaneOrder.symm :=
      Equiv.coe_reindexGL suPlaneOrder K (planeQuat h x)
    constructor
    · rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one, hcoe,
        Matrix.det_submatrix_equiv_self suPlaneOrder.symm]
      exact planeQuat_det_matrix h x
    · rw [hcoe, ← Matrix.submatrix_map, Matrix.transpose_submatrix,
        Matrix.submatrix_mul_equiv
          (((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (· ^ 3))ᵀ
          ((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          suPlaneOrder.symm suPlaneOrder.symm suPlaneOrder.symm,
        planeQuat_unitary h x, Matrix.submatrix_one_equiv]
  · rw [Subgroup.zpowers_le]
    apply Subgroup.subset_closure
    have hcoe : (((suPlaneOrder.reindexGL K).toMonoidHom planeSwap : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix
          suPlaneOrder.symm suPlaneOrder.symm :=
      Equiv.coe_reindexGL suPlaneOrder K planeSwap
    constructor
    · rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one, hcoe,
        Matrix.det_submatrix_equiv_self suPlaneOrder.symm]
      exact planeSwap_det_matrix
    · rw [hcoe, ← Matrix.submatrix_map, Matrix.transpose_submatrix,
        Matrix.submatrix_mul_equiv
          (((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (· ^ 3))ᵀ
          ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          suPlaneOrder.symm suPlaneOrder.symm suPlaneOrder.symm,
        planeSwap_unitary, Matrix.submatrix_one_equiv]

theorem isPGroup_suP0 {i : K} (h : i ^ 2 + 0 ^ 2 = -1) : IsPGroup 2 (suP0 h) :=
  (isPGroup_planeP0 h).map _

theorem adjoin_suP0_eq_top (hK : ringChar K ≠ 2) {i : K} (h : i ^ 2 + 0 ^ 2 = -1) :
    Algebra.adjoin K ((fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) ''
      (suP0 h : Set (GL (Fin 4) K))) = ⊤ := by
  have hset : ((fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) ''
      (suP0 h : Set (GL (Fin 4) K))) =
      (Matrix.reindexAlgEquiv K K suPlaneOrder) ''
        ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ''
            (planeP0 h : Set (GL (Fin 2 ⊕ Fin 2) K))) := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [suP0] at hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      refine ⟨(y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), ⟨y, hy, rfl⟩, ?_⟩
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
      exact (Equiv.coe_reindexGL suPlaneOrder K y).symm
    · rintro ⟨M, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨(suPlaneOrder.reindexGL K) y, ?_, ?_⟩
      · rw [suP0]
        exact Subgroup.mem_map_of_mem (suPlaneOrder.reindexGL K).toMonoidHom hy
      · rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
        exact Equiv.coe_reindexGL suPlaneOrder K y
  rw [hset, ← AlgEquiv.coe_toAlgHom, Algebra.adjoin_image, adjoin_planeP0_eq_top hK h,
    Algebra.map_top, AlgHom.range_eq_top]
  exact AlgEquiv.surjective _

theorem card_statedSU_four_three (hK : Nat.card K = 9) : Nat.card (StatedSU 4 3 K) = 13063680 := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h
    (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isSymm h
      (G := (1 : Matrix (Fin 4) (Fin 4) K)) (by simp))
    (CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft h (by simp))
    (Module.finrank_fin_fun _) (by norm_num)).2.1
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 17920 := by decide
  rw [hprod] at hSU
  norm_num at hSU
  rw [show StatedSU 4 3 K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 3 1 K 4 from rfl,
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h,
    CFSG.ClassicalGroups.UnitaryFlag.card_gramSU]
  exact_mod_cast hSU

theorem su4_three_adjoin_eq_top (hK : Nat.card K = 9) (P : Sylow 2 (StatedSU 4 3 K))
    (H : Subgroup (StatedSU 4 3 K)) (hPH : (P : Subgroup (StatedSU 4 3 K)) ≤ H) :
    Algebra.adjoin K (Set.range fun h : H => (((h : StatedSU 4 3 K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_nine hK
  obtain ⟨i, h⟩ := exists_sq_add_zero_sq_eq_neg_one hK
  exact adjoin_eq_top_of_sylow_le (suP0_le_statedSU h) (isPGroup_suP0 h)
    (adjoin_suP0_eq_top hK2 h) P hPH

theorem su4_three_eq_bot_of_normal_five (hK : Nat.card K = 9)
    (P : Sylow 2 (StatedSU 4 3 K)) (H : Subgroup (StatedSU 4 3 K))
    (hPH : (P : Subgroup (StatedSU 4 3 K)) ≤ H) {A : Subgroup H} [A.Normal] (hA : IsPGroup 5 A) :
    A = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_nine hK
  obtain ⟨i, h⟩ := exists_sq_add_zero_sq_eq_neg_one hK
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_le (suP0_le_statedSU h) (isPGroup_suP0 h) P hPH
  let φ : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 4) K := suPlaneOrder.reindexGL K
  have hmem (x : QuaternionGroup 2 × QuaternionGroup 2) : φ (planeQuat h x) ∈ suP0 h :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (planeQuat_mem_planeP0 h x)
  have hmemSwap : φ planeSwap ∈ suP0 h :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (planeSwap_mem_planeP0 h)
  have hx₁ : φ (planeQuat h (.a 1, 1)) ∈ suP0 h := hmem (.a 1, 1)
  have hy₁ : φ (planeQuat h (.xa 0, 1)) ∈ suP0 h := hmem (.xa 0, 1)
  have hx₂ : φ planeSwap ∈ suP0 h := hmemSwap
  have hy₂ : φ (planeQuat h (.xa 2, 1)) ∈ suP0 h := hmem (.xa 2, 1)
  let x₁ : StatedSU 4 3 K :=
    ⟨φ (planeQuat h (.a 1, 1)), suP0_le_statedSU h hx₁⟩
  let y₁ : StatedSU 4 3 K :=
    ⟨φ (planeQuat h (.xa 0, 1)), suP0_le_statedSU h hy₁⟩
  let x₂ : StatedSU 4 3 K := ⟨φ planeSwap, suP0_le_statedSU h hx₂⟩
  let y₂ : StatedSU 4 3 K :=
    ⟨φ (planeQuat h (.xa 2, 1)), suP0_le_statedSU h hy₂⟩
  refine eq_bot_of_normal_of_commute_commutator (G := StatedSU 4 3 K) (r := 5) ?_ hA
    g x₁ y₁ x₂ y₂ (hg x₁.val hx₁) (hg y₁.val hy₁)
    (hg x₂.val hx₂) (hg y₂.val hy₂) ?_
  · rw [card_statedSU_four_three hK]
    norm_num
  · intro b hb1 hb2 hb5
    let c : GL (Fin 2 ⊕ Fin 2) K := φ.symm (b : GL (Fin 4) K)
    have hb5' : (b : GL (Fin 4) K) ^ 5 = 1 := by
      have := congrArg (fun x : StatedSU 4 3 K => (x : GL (Fin 4) K)) hb5
      simpa using this
    have hc5 : c ^ 5 = 1 := by
      rw [show c = φ.symm (b : GL (Fin 4) K) from rfl, ← map_pow, hb5', map_one]
    have hcop : Nat.Coprime 5 (Nat.card K - 1) := by rw [hK]; norm_num
    have hz : Commute c (planeQuat h (.a 2, 1)) := by
      have hb1' : Commute (b : GL (Fin 4) K)
          (((⁅x₁, y₁⁆ : StatedSU 4 3 K)) : GL (Fin 4) K) :=
        hb1.map (Subgroup.subtype (StatedSU 4 3 K))
      have hmap := hb1'.map φ.symm
      have hcomm : (((⁅x₁, y₁⁆ : StatedSU 4 3 K)) : GL (Fin 4) K) =
          ⁅φ (planeQuat h (.a 1, 1)), φ (planeQuat h (.xa 0, 1))⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hcomm] at hmap
      have hmap' : φ.symm ⁅φ (planeQuat h (.a 1, 1)), φ (planeQuat h (.xa 0, 1))⁆ =
          planeQuat h (.a 2, 1) := by
        rw [map_commutatorElement φ.symm]
        simp only [MulEquiv.symm_apply_apply, commutatorElement_planeQuat_z h]
      rwa [hmap'] at hmap
    have hw : Commute c (planeQuat h (.xa 0, .xa 2)) := by
      have hb2' : Commute (b : GL (Fin 4) K)
          (((⁅x₂, y₂⁆ : StatedSU 4 3 K)) : GL (Fin 4) K) :=
        hb2.map (Subgroup.subtype (StatedSU 4 3 K))
      have hmap := hb2'.map φ.symm
      have hcomm : (((⁅x₂, y₂⁆ : StatedSU 4 3 K)) : GL (Fin 4) K) =
          ⁅φ planeSwap, φ (planeQuat h (.xa 2, 1))⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hcomm] at hmap
      have hmap' : φ.symm ⁅φ planeSwap, φ (planeQuat h (.xa 2, 1))⁆ =
          planeQuat h (.xa 0, .xa 2) := by
        rw [map_commutatorElement φ.symm]
        simp only [MulEquiv.symm_apply_apply, commutatorElement_planeSwap_w h]
      rwa [hmap'] at hmap
    have hc1 : c = 1 := eq_one_of_commute_z_w_of_pow_eq_one hK2 h (r := 5) hcop hz hw hc5
    have hbval : (b : GL (Fin 4) K) = 1 := by
      have hgoal := congrArg (fun z : GL (Fin 2 ⊕ Fin 2) K => φ z) hc1
      simpa [c] using hgoal
    exact Subtype.ext hbval

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
