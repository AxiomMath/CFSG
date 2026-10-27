module

public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def planeDiagSL :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →*
      SpecialLinearGroup (Fin 2 ⊕ Fin 2) K where
  toFun x := ⟨fromBlocks (x.1 : Matrix (Fin 2) (Fin 2) K) 0 0 (x.2 : Matrix (Fin 2) (Fin 2) K),
    by rw [det_fromBlocks_zero₂₁, SpecialLinearGroup.det_coe, SpecialLinearGroup.det_coe,
      one_mul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change fromBlocks _ 0 0 _ = fromBlocks _ 0 0 _ * fromBlocks _ 0 0 _
    rw [fromBlocks_multiply]
    simp

@[expose] noncomputable def planeDiag :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K :=
  SpecialLinearGroup.toGL.comp planeDiagSL

theorem coe_planeDiag (x : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    ((planeDiag x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (x.1 : Matrix (Fin 2) (Fin 2) K) 0 0 (x.2 : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] noncomputable def planeQuat {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 × QuaternionGroup 2 →* GL (Fin 2 ⊕ Fin 2) K :=
  planeDiag.comp ((quatHom h).prodMap (quatHom h))

theorem coe_planeQuat {a b : K} (h : a ^ 2 + b ^ 2 = -1) (x : QuaternionGroup 2 × QuaternionGroup 2) :
    ((planeQuat h x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (quatHom h x.1 : Matrix (Fin 2) (Fin 2) K) 0 0
        (quatHom h x.2 : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def planeSwap : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

theorem coe_planeSwap :
    ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 0 1 1 0 :=
  rfl

theorem planeSwap_mul_self : (planeSwap : GL (Fin 2 ⊕ Fin 2) K) * planeSwap = 1 :=
  Units.ext (by rw [Units.val_mul, coe_planeSwap, fromBlocks_multiply]; simp)

theorem planeSwap_conj_planeQuat {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (x : QuaternionGroup 2 × QuaternionGroup 2) :
    planeSwap * planeQuat h x * planeSwap⁻¹ = planeQuat h x.swap := by
  have hss : (planeSwap : GL (Fin 2 ⊕ Fin 2) K)⁻¹ = planeSwap :=
    inv_eq_of_mul_eq_one_right planeSwap_mul_self
  rw [hss]
  apply Units.ext
  simp only [Units.val_mul, coe_planeSwap, coe_planeQuat, fromBlocks_multiply,
    mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, Prod.fst_swap, Prod.snd_swap]

private theorem planeSwap_conj_planeQuat_self {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (x : QuaternionGroup 2 × QuaternionGroup 2) :
    planeSwap * planeQuat h x * planeSwap = planeQuat h x.swap := by
  rw [← planeSwap_conj_planeQuat h x, inv_eq_of_mul_eq_one_right planeSwap_mul_self]

@[expose] noncomputable def planeP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
  (planeQuat h).range ⊔ Subgroup.zpowers planeSwap

theorem planeQuat_mem_planeP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (x : QuaternionGroup 2 × QuaternionGroup 2) : planeQuat h x ∈ planeP0 h :=
  Subgroup.mem_sup_left ⟨x, rfl⟩

theorem planeSwap_mem_planeP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1) : planeSwap ∈ planeP0 h :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers planeSwap)

theorem isPGroup_planeP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1) : IsPGroup 2 (planeP0 h) := by
  have hQ : IsPGroup 2 (planeQuat h).range := by
    have hcard : Nat.card (QuaternionGroup 2 × QuaternionGroup 2) = 2 ^ 6 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    have hbase : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := IsPGroup.of_card hcard
    let q : QuaternionGroup 2 × QuaternionGroup 2 →* GL (Fin 2 ⊕ Fin 2) K := planeQuat h
    have hmap : IsPGroup 2 (Subgroup.map q ⊤) :=
      IsPGroup.map (p := 2) (H := ⊤) (hbase.to_subgroup ⊤) q
    have hq : q = planeQuat h := rfl
    rw [hq] at hmap
    rw [MonoidHom.range_eq_map]
    exact hmap
  have hS : IsPGroup 2 (Subgroup.zpowers (planeSwap : GL (Fin 2 ⊕ Fin 2) K)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one (x := (planeSwap : GL (Fin 2 ⊕ Fin 2) K))
      (by rw [sq, planeSwap_mul_self])
  have hN : Subgroup.zpowers (planeSwap : GL (Fin 2 ⊕ Fin 2) K) ≤
      Subgroup.normalizer (planeQuat h).range := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.swap, by rw [← hx]; exact (planeSwap_conj_planeQuat h x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x.swap, ?_⟩
      have h1 : planeSwap * (planeSwap * y * planeSwap) * planeSwap = y := by
        calc planeSwap * (planeSwap * y * planeSwap) * planeSwap
            = (planeSwap * planeSwap) * y * (planeSwap * planeSwap) := by group
          _ = y := by rw [planeSwap_mul_self]; simp
      have hy : y = planeSwap * planeQuat h x * planeSwap := by
        rw [hx, inv_eq_of_mul_eq_one_right planeSwap_mul_self]
        exact h1.symm
      rw [hy, planeSwap_conj_planeQuat_self h x]
  rw [show planeP0 h =
    (planeQuat h).range ⊔ Subgroup.zpowers (planeSwap : GL (Fin 2 ⊕ Fin 2) K) from rfl]
  exact IsPGroup.to_sup_of_normal_left' hQ hS hN

private theorem fromBlocks_zero_zero_mul_planeSwap (X : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks X 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 X 0 0 := by
  rw [coe_planeSwap, fromBlocks_multiply]
  simp

private theorem planeSwap_mul_fromBlocks_zero_zero (X : Matrix (Fin 2) (Fin 2) K) :
    ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (fromBlocks X 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 0 X 0 := by
  rw [coe_planeSwap, fromBlocks_multiply]
  simp

private theorem fromBlocks_zero_zero_X_zero_mul_planeSwap (X : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks 0 0 X 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 0 0 X := by
  rw [coe_planeSwap, fromBlocks_multiply]
  simp

private theorem planeSwap_mul_fromBlocks_zero_zero_mul_planeSwap
    (X : Matrix (Fin 2) (Fin 2) K) :
    ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (fromBlocks X 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks 0 0 0 X := by
  rw [planeSwap_mul_fromBlocks_zero_zero, fromBlocks_zero_zero_X_zero_mul_planeSwap]

private theorem fromBlocks_one_zero_mul_planeQuat {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (x : QuaternionGroup 2) :
    (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((planeQuat h (x, 1) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (quatHom h x) 0 0 0 := by
  rw [coe_planeQuat, fromBlocks_multiply]
  simp

private theorem fromBlocks_sub (A B : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks (A - B) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks A 0 0 0 - fromBlocks B 0 0 0 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp

private theorem fromBlocks_add' (A B : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks (A + B) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks A 0 0 0 + fromBlocks B 0 0 0 := by
  rw [fromBlocks_add]
  simp

private theorem fromBlocks_smul' (c : K) (A : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks (c • A) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      c • fromBlocks A 0 0 0 := by
  rw [fromBlocks_smul]
  simp

private theorem fromBlocks_eq_sum_blocks (A B C D : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks A B C D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks A 0 0 0 + fromBlocks 0 B 0 0 + fromBlocks 0 0 C 0 + fromBlocks 0 0 0 D := by
  rw [fromBlocks_add, fromBlocks_add, fromBlocks_add]
  simp

private theorem fromBlocks_sum {ι : Type*} [Fintype ι]
    (s : ι → Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks (∑ i, s i) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ∑ i, (fromBlocks (s i) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.sum_apply]

private theorem single_zero_zero {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) :
    (Matrix.single (0 : Fin 2) 0 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (2⁻¹ : K) • ((1 : Matrix (Fin 2) (Fin 2) K) - a • quatJ a b -
        b • (quatI K * quatJ a b)) := by
  have hsq : a * a + b * b = -1 := by simpa [sq] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, Matrix.smul_apply]
  all_goals
    first
      | (right; linear_combination -hsq)
      | (right; linear_combination hsq)
      | (right; ring)
      | (field_simp; linear_combination -hsq)
      | (field_simp; linear_combination hsq)

private theorem single_zero_one {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) :
    (Matrix.single (0 : Fin 2) 1 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (2⁻¹ : K) • (quatI K + a • (quatI K * quatJ a b) - b • quatJ a b) := by
  have hsq : a * a + b * b = -1 := by simpa [sq] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, Matrix.smul_apply]
  all_goals
    first
      | (right; linear_combination -hsq)
      | (right; linear_combination hsq)
      | (right; ring)
      | (field_simp; linear_combination -hsq)
      | (field_simp; linear_combination hsq)

private theorem single_one_zero {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) :
    (Matrix.single (1 : Fin 2) 0 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (2⁻¹ : K) • (a • (quatI K * quatJ a b) - b • quatJ a b - quatI K) := by
  have hsq : a * a + b * b = -1 := by simpa [sq] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, Matrix.smul_apply]
  all_goals
    first
      | (right; linear_combination -hsq)
      | (right; linear_combination hsq)
      | (right; ring)
      | (field_simp; linear_combination -hsq)
      | (field_simp; linear_combination hsq)

private theorem single_one_one {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) :
    (Matrix.single (1 : Fin 2) 1 (1 : K) : Matrix (Fin 2) (Fin 2) K) =
      (2⁻¹ : K) • ((1 : Matrix (Fin 2) (Fin 2) K) + a • quatJ a b +
        b • (quatI K * quatJ a b)) := by
  have hsq : a * a + b * b = -1 := by simpa [sq] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, Matrix.smul_apply]
  all_goals
    first
      | (right; linear_combination -hsq)
      | (right; linear_combination hsq)
      | (right; ring)
      | (field_simp; linear_combination -hsq)
      | (field_simp; linear_combination hsq)

private theorem fromBlocks_mem_of_mem {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : K) ≠ 0)
    {S : Subalgebra K (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)}
    (hp1 : (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S)
    (hq : ∀ x : QuaternionGroup 2, (fromBlocks (quatHom h x) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (fromBlocks X 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
  have h1 : (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := hp1
  have hI : (fromBlocks (quatI K) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    rw [← quatHom_a_one h]
    exact hq (.a 1)
  have hJ : (fromBlocks (quatJ a b) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    rw [← quatHom_xa_zero h]
    exact hq (.xa 0)
  have hIJ : (fromBlocks (quatI K * quatJ a b) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    rw [← quatHom_xa_three h]
    exact hq (.xa 3)
  have hs00 : (fromBlocks (Matrix.single (0 : Fin 2) 0 (1 : K)) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    have hW : (fromBlocks ((1 : Matrix (Fin 2) (Fin 2) K) - a • quatJ a b -
        b • (quatI K * quatJ a b)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
      rw [fromBlocks_sub, fromBlocks_sub, fromBlocks_smul', fromBlocks_smul']
      exact S.sub_mem (S.sub_mem h1 (S.smul_mem hJ a)) (S.smul_mem hIJ b)
    have hEq : (fromBlocks (Matrix.single (0 : Fin 2) 0 (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (2⁻¹ : K) • (fromBlocks ((1 : Matrix (Fin 2) (Fin 2) K) - a • quatJ a b -
          b • (quatI K * quatJ a b)) 0 0 0 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [single_zero_zero h h2, fromBlocks_smul']
    rw [hEq]
    exact S.smul_mem hW (2⁻¹)
  have hs01 : (fromBlocks (Matrix.single (0 : Fin 2) 1 (1 : K)) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    have hW : (fromBlocks (quatI K + a • (quatI K * quatJ a b) - b • quatJ a b) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
      rw [fromBlocks_sub, fromBlocks_add', fromBlocks_smul', fromBlocks_smul']
      exact S.sub_mem (S.add_mem hI (S.smul_mem hIJ a)) (S.smul_mem hJ b)
    have hEq : (fromBlocks (Matrix.single (0 : Fin 2) 1 (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (2⁻¹ : K) • (fromBlocks (quatI K + a • (quatI K * quatJ a b) -
          b • quatJ a b) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [single_zero_one h h2, fromBlocks_smul']
    rw [hEq]
    exact S.smul_mem hW (2⁻¹)
  have hs10 : (fromBlocks (Matrix.single (1 : Fin 2) 0 (1 : K)) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    have hW : (fromBlocks (a • (quatI K * quatJ a b) - b • quatJ a b - quatI K) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
      rw [fromBlocks_sub, fromBlocks_sub, fromBlocks_smul', fromBlocks_smul']
      exact S.sub_mem (S.sub_mem (S.smul_mem hIJ a) (S.smul_mem hJ b)) hI
    have hEq : (fromBlocks (Matrix.single (1 : Fin 2) 0 (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (2⁻¹ : K) • (fromBlocks (a • (quatI K * quatJ a b) - b • quatJ a b -
          quatI K) 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [single_one_zero h h2, fromBlocks_smul']
    rw [hEq]
    exact S.smul_mem hW (2⁻¹)
  have hs11 : (fromBlocks (Matrix.single (1 : Fin 2) 1 (1 : K)) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    have hW : (fromBlocks ((1 : Matrix (Fin 2) (Fin 2) K) + a • quatJ a b +
        b • (quatI K * quatJ a b)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
      rw [fromBlocks_add', fromBlocks_add', fromBlocks_smul', fromBlocks_smul']
      exact S.add_mem (S.add_mem h1 (S.smul_mem hJ a)) (S.smul_mem hIJ b)
    have hEq : (fromBlocks (Matrix.single (1 : Fin 2) 1 (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (2⁻¹ : K) • (fromBlocks ((1 : Matrix (Fin 2) (Fin 2) K) + a • quatJ a b +
          b • (quatI K * quatJ a b)) 0 0 0 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [single_one_one h h2, fromBlocks_smul']
    rw [hEq]
    exact S.smul_mem hW (2⁻¹)
  have hsingle : ∀ i j : Fin 2,
      (fromBlocks (Matrix.single i j (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hs00
    · exact hs01
    · exact hs10
    · exact hs11
  rw [Matrix.matrix_eq_sum_single X, fromBlocks_sum]
  refine S.sum_mem fun i _ => ?_
  rw [fromBlocks_sum]
  refine S.sum_mem fun j _ => ?_
  have hEq : (fromBlocks (Matrix.single i j (X i j)) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      X i j • (fromBlocks (Matrix.single i j (1 : K)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have hsingle' : (Matrix.single i j (X i j) : Matrix (Fin 2) (Fin 2) K) =
        X i j • Matrix.single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsingle', fromBlocks_smul']
  rw [hEq]
  exact S.smul_mem (hsingle i j) (X i j)

theorem adjoin_planeP0_eq_top (hK : ringChar K ≠ 2) {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    Algebra.adjoin K ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) '' (planeP0 h : Set (GL (Fin 2 ⊕ Fin 2) K))) =
      ⊤ := by
  let S : Subalgebra K (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
    Algebra.adjoin K ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) '' (planeP0 h : Set (GL (Fin 2 ⊕ Fin 2) K)))
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hmem : ∀ g ∈ planeP0 h,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro g hg
    exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hg)
  have hp1 : (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    have hzcoeff : ((planeQuat h (.a 2, 1) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1 := by
      rw [coe_planeQuat]
      simp [quatHom_a_two h]
    have hz : (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
      rw [← hzcoeff]
      exact hmem _ (planeQuat_mem_planeP0 h (.a 2, 1))
    have hsub : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) -
        (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S :=
      S.sub_mem S.one_mem hz
    have h1mz : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) -
        (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (fromBlocks (2 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      simp [one_add_one_eq_two]
    have h2smul : (2⁻¹ : K) • (2 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp [smul_eq_mul, h2]
      · simp [hij]
    have hEq : (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (2⁻¹ : K) • ((1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) -
          (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1 :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
      rw [h1mz, ← fromBlocks_smul', h2smul]
    rw [hEq]
    exact S.smul_mem hsub (2⁻¹)
  have hq : ∀ x : QuaternionGroup 2, (fromBlocks (quatHom h x) 0 0 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro x
    rw [← fromBlocks_one_zero_mul_planeQuat h x]
    exact S.mul_mem hp1 (hmem _ (planeQuat_mem_planeP0 h (x, 1)))
  have hs : ((planeSwap : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S :=
    hmem _ (planeSwap_mem_planeP0 h)
  have h11 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (fromBlocks X 0 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S :=
    fun X => fromBlocks_mem_of_mem h h2 hp1 hq X
  have h12 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (fromBlocks 0 X 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro X
    rw [← fromBlocks_zero_zero_mul_planeSwap]
    exact S.mul_mem (h11 X) hs
  have h21 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (fromBlocks 0 0 X 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro X
    rw [← planeSwap_mul_fromBlocks_zero_zero]
    exact S.mul_mem hs (h11 X)
  have h22 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (fromBlocks 0 0 0 X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ S := by
    intro X
    rw [← planeSwap_mul_fromBlocks_zero_zero_mul_planeSwap]
    exact S.mul_mem (S.mul_mem hs (h11 X)) hs
  have hS : S = ⊤ := by
    rw [eq_top_iff]
    intro M _
    rw [← Matrix.fromBlocks_toBlocks M, fromBlocks_eq_sum_blocks]
    exact S.add_mem (S.add_mem (S.add_mem (h11 _) (h12 _)) (h21 _)) (h22 _)
  exact hS

theorem commutatorElement_planeQuat_z {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    ⁅planeQuat h (.a 1, 1), planeQuat h (.xa 0, 1)⁆ = planeQuat h (.a 2, 1) := by
  rw [← map_commutatorElement]
  congr 1

theorem coe_planeQuat_z {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    ((planeQuat h (.a 2, 1) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (-1) 0 0 1 := by
  rw [coe_planeQuat, quatHom_a_two h, map_one, SpecialLinearGroup.coe_one]

theorem commutatorElement_planeSwap_w {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    ⁅(planeSwap : GL (Fin 2 ⊕ Fin 2) K), planeQuat h (.xa 2, 1)⁆ = planeQuat h (.xa 0, .xa 2) := by
  rw [commutatorElement_def, planeSwap_conj_planeQuat, ← map_inv, ← map_mul]
  congr 1

theorem coe_planeQuat_w {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    ((planeQuat h (.xa 0, .xa 2) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (quatJ a b) 0 0 (-quatJ a b) := by
  rw [coe_planeQuat, quatHom_xa_zero h, quatHom_xa_two h]

private theorem eq_fromBlocks_diag_of_commute_negOne_one (hK : ringChar K ≠ 2)
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : M * (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1) =
      (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 1) * M) :
    M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h := hM
  rw [← fromBlocks_toBlocks M] at h
  rw [fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [neg_mul, mul_neg, one_mul, mul_one, zero_mul, mul_zero, add_zero,
    zero_add] at h
  have hB : M.toBlocks₁₂ = -M.toBlocks₁₂ := (fromBlocks_inj.mp h).2.1
  have hC : -M.toBlocks₂₁ = M.toBlocks₂₁ := (fromBlocks_inj.mp h).2.2.1
  have hB0 : M.toBlocks₁₂ = 0 := by
    ext i j
    have hij : M.toBlocks₁₂ i j = -(M.toBlocks₁₂ i j) := by
      simpa using congrFun (congrFun hB i) j
    have hsum : M.toBlocks₁₂ i j + M.toBlocks₁₂ i j = 0 := by
      nth_rewrite 2 [hij]
      exact add_neg_cancel _
    have h2m : (2 : K) * M.toBlocks₁₂ i j = 0 := by
      rw [two_mul]
      exact hsum
    exact (mul_eq_zero.mp h2m).resolve_left h2
  have hC0 : M.toBlocks₂₁ = 0 := by
    ext i j
    have hij : -(M.toBlocks₂₁ i j) = M.toBlocks₂₁ i j := by
      simpa using congrFun (congrFun hC i) j
    have hsum : M.toBlocks₂₁ i j + M.toBlocks₂₁ i j = 0 := by
      nth_rewrite 1 [← hij]
      exact neg_add_cancel _
    have h2m : (2 : K) * M.toBlocks₂₁ i j = 0 := by
      rw [two_mul]
      exact hsum
    exact (mul_eq_zero.mp h2m).resolve_left h2
  calc M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
        (fromBlocks_toBlocks M).symm
    _ = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by rw [hB0, hC0]

private theorem exists_fromBlocks_of_commute_z (hK : ringChar K ≠ 2)
    {g z : GL (Fin 2 ⊕ Fin 2) K} (hz : Commute g z)
    (hzmat : (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (-1) 0 0 1) :
    ∃ A D : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks A 0 0 D := by
  have hcomm : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hz.eq]
  rw [hzmat] at hcomm
  exact ⟨_, _, eq_fromBlocks_diag_of_commute_negOne_one hK hcomm⟩

private theorem fromBlocks_pow_diag {A D : Matrix (Fin 2) (Fin 2) K} (n : ℕ) :
    (fromBlocks A 0 0 D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ n =
      fromBlocks (A ^ n) 0 0 (D ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, fromBlocks_one]
  | succ n ih =>
    rw [pow_succ, ih, fromBlocks_multiply, pow_succ, pow_succ]
    simp only [mul_zero, zero_mul, add_zero, zero_add]

private theorem blocks_mul_eq_one {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A D A' D' : Matrix (Fin 2) (Fin 2) K}
    (hM : M = fromBlocks A 0 0 D) (hN : N = fromBlocks A' 0 0 D') (h : M * N = 1) :
    A * A' = 1 ∧ D * D' = 1 := by
  rw [hM, hN] at h
  rw [fromBlocks_multiply, ← fromBlocks_one] at h
  simp only [mul_zero, zero_mul, add_zero, zero_add] at h
  rw [fromBlocks_inj] at h
  exact ⟨h.1, h.2.2.2⟩

private theorem blocks_pow_eq_one {r : ℕ} {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A D : Matrix (Fin 2) (Fin 2) K} (hM : M = fromBlocks A 0 0 D) (h : M ^ r = 1) :
    A ^ r = 1 ∧ D ^ r = 1 := by
  rw [hM, fromBlocks_pow_diag, ← fromBlocks_one, fromBlocks_inj] at h
  exact ⟨h.1, h.2.2.2⟩

private theorem blocks_eq_one_of_pow_eq_one {r : ℕ}
    (hr : Nat.Coprime r (Nat.card (GL (Fin 2) K)))
    {A D A' D' : Matrix (Fin 2) (Fin 2) K}
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (hDD' : D * D' = 1) (hD'D : D' * D = 1)
    (hAr : A ^ r = 1) (hDr : D ^ r = 1) : A = 1 ∧ D = 1 := by
  constructor
  · let Au : GL (Fin 2) K := Units.mk A A' hAA' hA'A
    have hAu : (Au : Matrix (Fin 2) (Fin 2) K) = A := rfl
    have hAur : Au ^ r = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hAu, hAr, Units.val_one]
    have dvd1 : orderOf Au ∣ r := orderOf_dvd_of_pow_eq_one hAur
    have dvd2 : orderOf Au ∣ Nat.card (GL (Fin 2) K) := orderOf_dvd_natCard Au
    have hone : orderOf Au = 1 := Nat.eq_one_of_dvd_coprimes hr dvd1 dvd2
    have hAu1 : Au = 1 := orderOf_eq_one_iff.mp hone
    rw [← hAu, hAu1, Units.val_one]
  · let Du : GL (Fin 2) K := Units.mk D D' hDD' hD'D
    have hDu : (Du : Matrix (Fin 2) (Fin 2) K) = D := rfl
    have hDur : Du ^ r = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hDu, hDr, Units.val_one]
    have dvd1 : orderOf Du ∣ r := orderOf_dvd_of_pow_eq_one hDur
    have dvd2 : orderOf Du ∣ Nat.card (GL (Fin 2) K) := orderOf_dvd_natCard Du
    have hone : orderOf Du = 1 := Nat.eq_one_of_dvd_coprimes hr dvd1 dvd2
    have hDu1 : Du = 1 := orderOf_eq_one_iff.mp hone
    rw [← hDu, hDu1, Units.val_one]

theorem eq_one_of_commute_z_of_pow_eq_one [Finite K] (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) {r : ℕ} (hr : Nat.Coprime r (Nat.card (GL (Fin 2) K)))
    {g : GL (Fin 2 ⊕ Fin 2) K} (hz : Commute g (planeQuat h (.a 2, 1))) (hg : g ^ r = 1) :
    g = 1 := by
  let z : GL (Fin 2 ⊕ Fin 2) K := planeQuat h (.a 2, 1)
  have hz' : Commute g z := hz
  have hzmat : (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (-1) 0 0 1 :=
    coe_planeQuat_z h
  obtain ⟨A, D, hM⟩ := exists_fromBlocks_of_commute_z hK hz' hzmat
  obtain ⟨A', D', hMinv⟩ := exists_fromBlocks_of_commute_z hK hz'.inv_left hzmat
  have hprod : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hprodinv : ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpow : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]
  obtain ⟨hAA', hDD'⟩ := blocks_mul_eq_one hM hMinv hprod
  obtain ⟨hA'A, hD'D⟩ := blocks_mul_eq_one hMinv hM hprodinv
  obtain ⟨hAr, hDr⟩ := blocks_pow_eq_one hM hpow
  obtain ⟨hA1, hD1⟩ := blocks_eq_one_of_pow_eq_one hr hAA' hA'A hDD' hD'D hAr hDr
  apply Units.ext
  rw [hM, hA1, hD1, fromBlocks_one, Units.val_one]

private theorem eq_zero_of_mul_add_mul_comm (hK : ringChar K ≠ 2) {a : K} (ha : a ≠ 0)
    {x : K} (hx : x * a + a * x = 0) : x = 0 := by
  have h2a : (2 : K) * a ≠ 0 := mul_ne_zero (Ring.two_ne_zero hK) ha
  have hsum : x * a + x * a = 0 := by
    rw [← mul_comm x a] at hx
    exact hx
  have hzero : x * (2 * a) = 0 := by
    rw [mul_comm (2 : K) a, ← mul_assoc, mul_two, hsum]
  exact (mul_eq_zero.mp hzero).resolve_right h2a

private theorem offdiag_eq_zero_of_commute_quatJ (hK : ringChar K ≠ 2) {a : K} (ha : a ≠ 0)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A * quatJ a 0 = quatJ a 0 * A) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  have h01 : A 0 1 * (-a) = a * A 0 1 := by
    have h := congrFun (congrFun hA 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, quatJ] using h
  have h10 : A 1 0 * a = (-a) * A 1 0 := by
    have h := congrFun (congrFun hA 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, quatJ] using h
  constructor
  · apply eq_zero_of_mul_add_mul_comm hK ha
    rw [mul_neg] at h01
    have h01' : A 0 1 * a = -(a * A 0 1) := neg_eq_iff_eq_neg.mp h01
    rw [h01', neg_add_cancel]
  · apply eq_zero_of_mul_add_mul_comm hK ha
    have h10' : A 1 0 * a = -(a * A 1 0) := by
      rw [neg_mul] at h10
      exact h10
    rw [h10', neg_add_cancel]

private theorem eq_diagonal_of_offdiag_eq_zero {A : Matrix (Fin 2) (Fin 2) K}
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) : A = diagonal (fun i => A i i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

private theorem fromBlocks_diagonal {u v : Fin 2 → K} :
    (fromBlocks (diagonal u) 0 0 (diagonal v) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      diagonal (Sum.elim u v) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply]

private theorem blocks_of_commute_fromBlocks {A D J : Matrix (Fin 2) (Fin 2) K}
    (h : (fromBlocks A 0 0 D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          fromBlocks J 0 0 (-J) = fromBlocks J 0 0 (-J) * fromBlocks A 0 0 D) :
    A * J = J * A ∧ D * J = J * D := by
  rw [fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [neg_mul, mul_neg, zero_mul, mul_zero, neg_zero, add_zero,
    zero_add] at h
  rw [fromBlocks_inj] at h
  exact ⟨h.1, neg_inj.mp h.2.2.2⟩

theorem eq_one_of_commute_z_w_of_pow_eq_one [Finite K] (hK : ringChar K ≠ 2) {a : K}
    (h : a ^ 2 + 0 ^ 2 = -1) {r : ℕ} (hr : Nat.Coprime r (Nat.card K - 1))
    {g : GL (Fin 2 ⊕ Fin 2) K} (hz : Commute g (planeQuat h (.a 2, 1)))
    (hw : Commute g (planeQuat h (.xa 0, .xa 2))) (hg : g ^ r = 1) : g = 1 := by
  have ha : a ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have h3 : 3 ≤ Nat.card K := by
    have hne1 : (1 : K) ≠ -1 := fun hh => Ring.neg_one_ne_one_of_char_ne_two hK hh.symm
    have hne0 : (0 : K) ≠ 1 := zero_ne_one
    have hne0' : (0 : K) ≠ -1 := by
      intro h0
      have h1 : (1 : K) = 0 := by rw [← neg_neg (1 : K), ← h0, neg_zero]
      exact one_ne_zero h1
    have hinj : Function.Injective (fun i : Fin 3 => (![0, 1, -1] : Fin 3 → K) i) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin] at h
  have hr0 : r ≠ 0 := by
    intro h0
    have h1 : Nat.card K - 1 = 1 := (Nat.coprime_zero_left _).mp (h0 ▸ hr)
    omega
  let z : GL (Fin 2 ⊕ Fin 2) K := planeQuat h (.a 2, 1)
  have hz' : Commute g z := hz
  have hzmat : (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (-1) 0 0 1 :=
    coe_planeQuat_z h
  obtain ⟨A, D, hM⟩ := exists_fromBlocks_of_commute_z hK hz' hzmat
  let w : GL (Fin 2 ⊕ Fin 2) K := planeQuat h (.xa 0, .xa 2)
  have hw' : Commute g w := hw
  have hwmat : (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (quatJ a 0) 0 0 (-quatJ a 0) := coe_planeQuat_w h
  have hcommW : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hw'.eq]
  have hcommW' : (fromBlocks A 0 0 D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks (quatJ a 0) 0 0 (-quatJ a 0) =
      fromBlocks (quatJ a 0) 0 0 (-quatJ a 0) * fromBlocks A 0 0 D := by
    rw [← hM, ← hwmat]
    exact hcommW
  obtain ⟨hAJ, hDJ⟩ := blocks_of_commute_fromBlocks hcommW'
  obtain ⟨hA01, hA10⟩ := offdiag_eq_zero_of_commute_quatJ hK ha hAJ
  obtain ⟨hD01, hD10⟩ := offdiag_eq_zero_of_commute_quatJ hK ha hDJ
  have hAdiag : A = diagonal (fun i => A i i) := eq_diagonal_of_offdiag_eq_zero hA01 hA10
  have hDdiag : D = diagonal (fun i => D i i) := eq_diagonal_of_offdiag_eq_zero hD01 hD10
  let d : Fin 2 ⊕ Fin 2 → K := Sum.elim (fun i => A i i) (fun i => D i i)
  have hMd : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = diagonal d := by
    rw [hM, hAdiag, hDdiag, fromBlocks_diagonal]
  have hpowM : (diagonal d : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ r = 1 := by
    rw [← hMd, ← Units.val_pow_eq_pow_val, hg, Units.val_one]
  have hdr : d ^ r = 1 := by
    have h' := hpowM
    rw [Matrix.diagonal_pow, Matrix.diagonal_eq_one] at h'
    exact h'
  have hd1 : ∀ k, d k = 1 := by
    intro k
    have hk : d k ^ r = 1 := by
      have h' := congrFun hdr k
      simpa using h'
    have hk0 : d k ≠ 0 := by
      intro h0
      rw [h0, zero_pow hr0] at hk
      exact zero_ne_one hk
    let u : Kˣ := Units.mk0 (d k) hk0
    have huval : ((u : Kˣ) : K) = d k := rfl
    have hu : u ^ r = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, huval, hk, Units.val_one]
    have dvd1 : orderOf u ∣ r := orderOf_dvd_of_pow_eq_one hu
    have dvd2 : orderOf u ∣ Nat.card K - 1 := by
      rw [← Nat.card_units K]
      exact orderOf_dvd_natCard u
    have hone : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hr dvd1 dvd2
    have hu1 : u = 1 := orderOf_eq_one_iff.mp hone
    calc d k = (u : K) := huval.symm
      _ = ((1 : Kˣ) : K) := by rw [hu1]
      _ = 1 := rfl
  have hd : d = 1 := funext hd1
  apply Units.ext
  rw [hMd, hd]
  show diagonal (fun _ => (1 : K)) =
    ((1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  rw [diagonal_one, Units.val_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
