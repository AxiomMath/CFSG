module

public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm

private theorem mul_six_assoc {M : Type*} [Semigroup M] (a b c d e f : M) :
    (a * b * c) * (d * e * f) = a * b * (c * d) * e * f := by
  calc (a * b * c) * (d * e * f)
      = a * (b * (c * (d * (e * f)))) := by simp only [mul_assoc]
    _ = a * (b * ((c * d) * (e * f))) := by rw [← mul_assoc c d (e * f)]
    _ = a * b * (c * d) * e * f := by simp only [mul_assoc]

private theorem slLower2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slLower2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

private theorem slUpper2Hom_transvection {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slUpper2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c := by
  rw [slUpper2Hom, MonoidHom.comp_apply, slUpperBlockHom_transvection,
    slUpperBlockHom_transvection]

private theorem graphAut_transvection_coe {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    (slGraphAut N F2 (SpecialLinearGroup.transvection hab (1 : F2)) :
        Matrix (Fin N) (Fin N) F2) = 1 + Matrix.single b a 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [slGraphAut_matrix, Matrix.SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, hneg]

private theorem matrix_eq_of_conj_graph_aut {N : ℕ}
    (c : SpecialLinearGroup (Fin N) F2) {a b u v : Fin N} (hab : a ≠ b) (huv : u ≠ v)
    (h : c * slGraphAut N F2 (SpecialLinearGroup.transvection hab 1) * c⁻¹ =
      SpecialLinearGroup.transvection huv 1) :
    (c : Matrix (Fin N) (Fin N) F2) * Matrix.single b a 1 *
      ((c⁻¹ : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) =
      Matrix.single u v 1 := by
  have hC : (c : Matrix (Fin N) (Fin N) F2) *
      ((c⁻¹ : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have key : (c : Matrix (Fin N) (Fin N) F2) * (1 + Matrix.single b a 1) *
      ((c⁻¹ : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) =
      1 + Matrix.single u v 1 := by
    have hh := congrArg (fun x : SpecialLinearGroup (Fin N) F2 =>
      (x : Matrix (Fin N) (Fin N) F2)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul, graphAut_transvection_coe hab,
      SpecialLinearGroup.transvection_coe] using hh
  rw [mul_add, add_mul, mul_one, hC] at key
  exact add_left_cancel key

private theorem not_conj_graph_core {N : ℕ} {C C' : Matrix (Fin N) (Fin N) F2}
    (hC : C * C' = 1) (hC' : C' * C = 1)
    {p q r p' q' r' : Fin N} (hqr : q' ≠ r')
    (h1 : C * Matrix.single q p 1 * C' = Matrix.single p' q' 1)
    (h2 : C * Matrix.single p r 1 * C' = Matrix.single r' p' 1)
    (h3 : C * Matrix.single q r 1 * C' = Matrix.single r' q' 1) : False := by
  have hprod : (C * Matrix.single q p 1 * C') * (C * Matrix.single p r 1 * C') =
      C * Matrix.single q r 1 * C' := by
    rw [mul_six_assoc C (Matrix.single q p 1) C' C (Matrix.single p r 1) C', hC',
      mul_one, mul_assoc C (Matrix.single q p 1) (Matrix.single p r 1),
      Matrix.single_mul_single_same]
    simp
  have hzero : Matrix.single r' q' (1 : F2) = 0 := by
    rw [← h3, ← hprod, h1, h2]
    exact Matrix.single_mul_single_of_ne (1 : F2) p' q' r' hqr 1
  have hne : Matrix.single r' q' (1 : F2) ≠ 0 := by
    intro hh
    have hh' := congrFun (congrFun hh r') q'
    simp [Matrix.single_apply] at hh'
  exact hne hzero

private theorem lower_equation {m : ℕ} (c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (h : ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      c * slGraphAut (m + 1 + 1 + 1) F2 (slLower2Hom m s) * c⁻¹ = slLower2Hom m s)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
        Matrix.single j.succ.succ i.succ.succ 1 *
        ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
          Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) =
      Matrix.single i.succ.succ j.succ.succ 1 := by
  have hh := h (SpecialLinearGroup.transvection hij 1)
  rw [slLower2Hom_transvection hij 1] at hh
  exact matrix_eq_of_conj_graph_aut c
    ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij))
    ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) hh

private theorem shift_equation {m : ℕ} (c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (h : ∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
      c * slGraphAut (m + 1 + 1 + 1) F2 (slUpper2Hom m s) * c⁻¹ = slLower2Hom m s)
    {i j : Fin (m + 1)} (hij : i ≠ j)
    (hi : i ∈ {j : Fin (m + 1) | 2 ≤ j.val}) (hj : j ∈ {j : Fin (m + 1) | 2 ≤ j.val}) :
    (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
        Matrix.single j.castSucc.castSucc i.castSucc.castSucc 1 *
        ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
          Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) =
      Matrix.single i.succ.succ j.succ.succ 1 := by
  have hh := h (SpecialLinearGroup.transvection hij 1)
    (transvection_mem_slOn hij 1 hi hj)
  rw [slUpper2Hom_transvection hij 1, slLower2Hom_transvection hij 1] at hh
  exact matrix_eq_of_conj_graph_aut c
    ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij))
    ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) hh

theorem not_conj_graph_lower {m : ℕ} (hm : 2 ≤ m)
    (c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
    ¬ ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      c * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (m + 1 + 1 + 1) F2
        (slLower2Hom m s) * c⁻¹ = slLower2Hom m s := by
  intro h
  let p : Fin (m + 1) := ⟨0, by omega⟩
  let q : Fin (m + 1) := ⟨1, by omega⟩
  let r : Fin (m + 1) := ⟨2, by omega⟩
  have hpq : p ≠ q := by
    intro hh
    have hval : p.val = q.val := congrArg Fin.val hh
    have hp0 : p.val = 0 := rfl
    have hq1 : q.val = 1 := rfl
    omega
  have hrp : r ≠ p := by
    intro hh
    have hval : r.val = p.val := congrArg Fin.val hh
    have hr2 : r.val = 2 := rfl
    have hp0 : p.val = 0 := rfl
    omega
  have hrq : r ≠ q := by
    intro hh
    have hval : r.val = q.val := congrArg Fin.val hh
    have hr2 : r.val = 2 := rfl
    have hq1 : q.val = 1 := rfl
    omega
  have hqr : q ≠ r := fun hh => hrq hh.symm
  have hC : (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
      ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hC' : ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
      (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  exact not_conj_graph_core hC hC'
    (p := p.succ.succ) (q := q.succ.succ) (r := r.succ.succ)
    (p' := p.succ.succ) (q' := q.succ.succ) (r' := r.succ.succ)
    ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hqr))
    (lower_equation c h hpq) (lower_equation c h hrp) (lower_equation c h hrq)

theorem not_conj_graph_shift {m : ℕ} (hm : 4 ≤ m)
    (c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
    ¬ ∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
      c * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (m + 1 + 1 + 1) F2
        (slUpper2Hom m s) * c⁻¹ = slLower2Hom m s := by
  intro h
  let p : Fin (m + 1) := ⟨2, by omega⟩
  let q : Fin (m + 1) := ⟨3, by omega⟩
  let r : Fin (m + 1) := ⟨4, by omega⟩
  have hpq : p ≠ q := by
    intro hh
    have hval : p.val = q.val := congrArg Fin.val hh
    have hp2 : p.val = 2 := rfl
    have hq3 : q.val = 3 := rfl
    omega
  have hrp : r ≠ p := by
    intro hh
    have hval : r.val = p.val := congrArg Fin.val hh
    have hr4 : r.val = 4 := rfl
    have hp2 : p.val = 2 := rfl
    omega
  have hrq : r ≠ q := by
    intro hh
    have hval : r.val = q.val := congrArg Fin.val hh
    have hr4 : r.val = 4 := rfl
    have hq3 : q.val = 3 := rfl
    omega
  have hqr : q ≠ r := fun hh => hrq hh.symm
  have hp : p ∈ {j : Fin (m + 1) | 2 ≤ j.val} := by
    show 2 ≤ p.val
    have hp2 : p.val = 2 := rfl
    omega
  have hq : q ∈ {j : Fin (m + 1) | 2 ≤ j.val} := by
    show 2 ≤ q.val
    have hq3 : q.val = 3 := rfl
    omega
  have hr : r ∈ {j : Fin (m + 1) | 2 ≤ j.val} := by
    show 2 ≤ r.val
    have hr4 : r.val = 4 := rfl
    omega
  have hC : (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
      ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hC' : ((c⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
      (c : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  exact not_conj_graph_core hC hC'
    (p := p.castSucc.castSucc) (q := q.castSucc.castSucc) (r := r.castSucc.castSucc)
    (p' := p.succ.succ) (q' := q.succ.succ) (r' := r.succ.succ)
    ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hqr))
    (shift_equation c h hpq hp hq) (shift_equation c h hrp hr hp)
    (shift_equation c h hrq hr hq)

end CFSG.StandardType.GGHalf

end
