module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2PslDefs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.NFa2

open scoped MatrixGroups

open Polynomial

variable (F : Type*) [Field F]

@[expose] def psl2GenS : SL(2, F) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; norm_num⟩

@[expose] def psl2GenT : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩

@[expose] def psl2GenNeg : SL(2, F) :=
  ⟨!![-1, 0; 0, -1], by rw [Matrix.det_fin_two_of]; norm_num⟩

@[expose] def psl2GenR : SL(2, F) :=
  psl2GenS F * psl2GenT F

@[expose] def psl2GenJ (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) : SL(2, F) :=
  ⟨!![x, x + z; z, -x], by rw [Matrix.det_fin_two_of]; linear_combination -h⟩

theorem psl2Gen_val_mul (A B : SL(2, F)) : (A * B).1 = A.1 * B.1 := rfl

theorem psl2GenS_val : (psl2GenS F).1 = !![0, -1; 1, 0] := rfl

theorem psl2GenT_val : (psl2GenT F).1 = !![1, 1; 0, 1] := rfl

theorem psl2GenNeg_val : (psl2GenNeg F).1 = !![-1, 0; 0, -1] := rfl

theorem psl2GenJ_val (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) :
    (psl2GenJ F x z h).1 = !![x, x + z; z, -x] := rfl

theorem psl2GenR_val : (psl2GenR F).1 = !![0, -1; 1, 1] := by
  simp only [psl2GenR, psl2Gen_val_mul, psl2GenS_val, psl2GenT_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem psl2GenT_pow_coe (n : ℕ) :
    ((psl2GenT F ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, (n : F); 0, 1] := by
  induction n with
  | zero => rw [pow_zero]; ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [psl2GenT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem psl2GenT_transvection (h : (0 : Fin 2) ≠ 1) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection h (n : F) = psl2GenT F ^ n := by
  apply Subtype.ext
  rw [psl2GenT_pow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

theorem psl2GenTransvection_10 (h : (1 : Fin 2) ≠ 0) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection h (-(n : F)) =
      psl2GenS F * psl2GenT F ^ n * (psl2GenS F)⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, psl2GenT_pow_coe,
    Matrix.SpecialLinearGroup.coe_inv]
  simp only [psl2GenS, Matrix.SpecialLinearGroup.coe_mk, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem psl2GenT_transvection_mem (hcast : ∀ c : F, ∃ n : ℕ, (n : F) = c)
    (h : (0 : Fin 2) ≠ 1) (c : F) :
    Matrix.SpecialLinearGroup.transvection h c ∈
      Subgroup.closure ({psl2GenS F, psl2GenT F} : Set SL(2, F)) := by
  obtain ⟨n, rfl⟩ := hcast c
  rw [psl2GenT_transvection F h n]
  exact pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _

theorem psl2GenTransvection_10_mem (hcast : ∀ c : F, ∃ n : ℕ, (n : F) = c)
    (h : (1 : Fin 2) ≠ 0) (c : F) :
    Matrix.SpecialLinearGroup.transvection h c ∈
      Subgroup.closure ({psl2GenS F, psl2GenT F} : Set SL(2, F)) := by
  obtain ⟨n, hn⟩ := hcast (-c)
  have hc : c = -(n : F) := by rw [hn, neg_neg]
  rw [hc, psl2GenTransvection_10 F h n]
  have hS := Subgroup.subset_closure (Set.mem_insert (psl2GenS F) {psl2GenT F})
  have hT := Subgroup.subset_closure
    (Set.mem_insert_of_mem (psl2GenS F) (Set.mem_singleton (psl2GenT F)))
  exact mul_mem (mul_mem hS (pow_mem hT _)) (inv_mem hS)

theorem psl2Gen_sl2_mem_closure (hcast : ∀ c : F, ∃ n : ℕ, (n : F) = c) (g : SL(2, F)) :
    g ∈ Subgroup.closure ({psl2GenS F, psl2GenT F} : Set SL(2, F)) := by
  refine Matrix.SL2.transvection_induction
    (fun A => A ∈ Subgroup.closure ({psl2GenS F, psl2GenT F} : Set SL(2, F))) ?_ ?_ g
  · intro i j h c
    fin_cases i <;> fin_cases j <;>
      first
      | exact (h rfl).elim
      | exact psl2GenT_transvection_mem F hcast h c
      | exact psl2GenTransvection_10_mem F hcast h c
  · intro A B hA hB
    exact mul_mem hA hB

theorem psl2Gen_eq_top_of (H : Subgroup (PSL(2, F)))
    (hcast : ∀ c : F, ∃ n : ℕ, (n : F) = c)
    (hS : (QuotientGroup.mk (psl2GenS F) : PSL(2, F)) ∈ H)
    (hT : (QuotientGroup.mk (psl2GenT F) : PSL(2, F)) ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have key : ∀ A ∈ Subgroup.closure ({psl2GenS F, psl2GenT F} : Set SL(2, F)),
      (QuotientGroup.mk A : PSL(2, F)) ∈ H := by
    intro A hA
    induction hA using Subgroup.closure_induction with
    | mem B hB =>
      rcases hB with rfl | rfl
      · exact hS
      · exact hT
    | one => rw [QuotientGroup.mk_one]; exact H.one_mem
    | mul A B _ _ hA hB => rw [QuotientGroup.mk_mul]; exact H.mul_mem hA hB
    | inv A _ hA => rw [QuotientGroup.mk_inv]; exact H.inv_mem hA
  exact key g (psl2Gen_sl2_mem_closure F hcast g)

theorem psl2Gen_exists_norm_neg_one [Fintype F] (hodd : Fintype.card F % 2 = 1)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0) :
    ∃ x z : F, x ^ 2 + x * z + z ^ 2 = -1 := by
  have hf : (X ^ 2 + C 4 : F[X]).degree = 2 := by
    exact_mod_cast degree_X_pow_add_C (by norm_num : 0 < 2) (4 : F)
  have hg : (C 3 * X ^ 2 : F[X]).degree = 2 := by
    exact_mod_cast degree_C_mul_X_pow 2 h3
  obtain ⟨u, w, huw⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at huw
  obtain ⟨x, hx⟩ : ∃ x : F, x = 2⁻¹ * (u - w) := ⟨_, rfl⟩
  have h2x : 2 * x = u - w := by rw [hx]; exact mul_inv_cancel_left₀ h2 _
  have key : (4 : F) * (x ^ 2 + x * w + w ^ 2 + 1) = 0 := by
    linear_combination huw + (2 * x + u + w) * h2x
  refine ⟨x, w, ?_⟩
  have h' := (mul_eq_zero.mp key).resolve_left h4
  linear_combination h'

theorem psl2GenS_mul_self : psl2GenS F * psl2GenS F = psl2GenNeg F := by
  apply Subtype.ext
  rw [psl2Gen_val_mul, psl2GenS_val, psl2GenNeg_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem psl2GenJ_mul_self (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) :
    psl2GenJ F x z h * psl2GenJ F x z h = psl2GenNeg F := by
  apply Subtype.ext
  rw [psl2Gen_val_mul, psl2GenJ_val, psl2GenNeg_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h

theorem psl2GenRJ_mul_self (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) :
    (psl2GenR F * psl2GenJ F x z h) * (psl2GenR F * psl2GenJ F x z h) = psl2GenNeg F := by
  apply Subtype.ext
  simp only [psl2Gen_val_mul, psl2GenR_val, psl2GenJ_val, psl2GenNeg_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h

theorem psl2GenNeg_mem_center : psl2GenNeg F ∈ Subgroup.center (SL(2, F)) := by
  rw [Subgroup.mem_center_iff]
  intro A
  apply Subtype.ext
  simp only [psl2Gen_val_mul, psl2GenNeg_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem psl2Gen_central_entries (g : SL(2, F)) (hg : g ∈ Subgroup.center (SL(2, F))) :
    g.1 1 0 = 0 ∧ g.1 0 1 = 0 := by
  have hT := congrArg Subtype.val (Subgroup.mem_center_iff.mp hg (psl2GenT F))
  have hS := congrArg Subtype.val (Subgroup.mem_center_iff.mp hg (psl2GenS F))
  simp only [psl2Gen_val_mul, psl2GenT_val, psl2GenS_val] at hT hS
  have e1 := congrFun (congrFun hT 0) 0
  have e2 := congrFun (congrFun hS 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
  exact ⟨e1, by linear_combination -e2 - e1⟩

theorem psl2GenS_not_mem_center : psl2GenS F ∉ Subgroup.center (SL(2, F)) := by
  intro hc
  have h := (psl2Gen_central_entries F _ hc).1
  simp [psl2GenS_val] at h

theorem psl2GenJ_not_mem_center (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) :
    psl2GenJ F x z h ∉ Subgroup.center (SL(2, F)) := by
  intro hc
  obtain ⟨h10, h01⟩ := psl2Gen_central_entries F _ hc
  simp only [psl2GenJ_val] at h10 h01
  have hz : z = 0 := by simpa using h10
  have hx : x = 0 := by
    have h01' : x + z = 0 := by simpa using h01
    linear_combination h01' - hz
  rw [hx, hz] at h
  norm_num at h

theorem psl2GenRJ_not_mem_center (x z : F) (h : x ^ 2 + x * z + z ^ 2 = -1) :
    psl2GenR F * psl2GenJ F x z h ∉ Subgroup.center (SL(2, F)) := by
  intro hc
  obtain ⟨h10, h01⟩ := psl2Gen_central_entries F _ hc
  simp only [psl2Gen_val_mul, psl2GenR_val, psl2GenJ_val] at h10 h01
  have h10' : x + z = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
  have h01' : x = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
  have hz : z = 0 := by linear_combination h10' - h01'
  rw [h01', hz] at h
  norm_num at h

theorem psl2Gen_orderOf_two (g : SL(2, F)) (hg : g * g = psl2GenNeg F)
    (hnc : g ∉ Subgroup.center (SL(2, F))) :
    orderOf (QuotientGroup.mk g : PSL(2, F)) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, sq, hg]
    exact (QuotientGroup.eq_one_iff _).mpr (psl2GenNeg_mem_center F)
  · intro h
    exact hnc ((QuotientGroup.eq_one_iff g).mp h)

theorem psl2Gen_main [Fintype F] (hcast : ∀ c : F, ∃ n : ℕ, (n : F) = c)
    (hodd : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h4 : (4 : F) ≠ 0) :
    ∃ i j k : PSL(2, F), orderOf i = 2 ∧ orderOf j = 2 ∧ orderOf k = 2 ∧
      Subgroup.closure ({i, j, k} : Set PSL(2, F)) = ⊤ := by
  obtain ⟨x, z, hxz⟩ := psl2Gen_exists_norm_neg_one F hodd h2 h3 h4
  refine ⟨QuotientGroup.mk (psl2GenS F), QuotientGroup.mk (psl2GenJ F x z hxz),
    QuotientGroup.mk (psl2GenR F * psl2GenJ F x z hxz), ?_, ?_, ?_, ?_⟩
  · exact psl2Gen_orderOf_two F _ (psl2GenS_mul_self F) (psl2GenS_not_mem_center F)
  · exact psl2Gen_orderOf_two F _ (psl2GenJ_mul_self F x z hxz)
      (psl2GenJ_not_mem_center F x z hxz)
  · exact psl2Gen_orderOf_two F _ (psl2GenRJ_mul_self F x z hxz)
      (psl2GenRJ_not_mem_center F x z hxz)
  · have hkj : (QuotientGroup.mk (psl2GenR F * psl2GenJ F x z hxz) : PSL(2, F)) *
        (QuotientGroup.mk (psl2GenJ F x z hxz) : PSL(2, F)) =
          (QuotientGroup.mk (psl2GenR F) : PSL(2, F)) := by
      rw [← QuotientGroup.mk_mul, mul_assoc, psl2GenJ_mul_self F x z hxz,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (psl2GenNeg F)).mpr
          (psl2GenNeg_mem_center F), mul_one]
    have hT : (QuotientGroup.mk (psl2GenT F) : PSL(2, F)) =
        (QuotientGroup.mk (psl2GenS F) : PSL(2, F))⁻¹ *
          (QuotientGroup.mk (psl2GenR F) : PSL(2, F)) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, psl2GenR, inv_mul_cancel_left]
    refine psl2Gen_eq_top_of F _ hcast ?_ ?_
    · exact Subgroup.subset_closure (by simp)
    · rw [hT]
      refine mul_mem (inv_mem ?_) ?_
      · exact Subgroup.subset_closure (by simp)
      · rw [← hkj]
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem psl2_gen_three_involutions : PslGenStmt := by
  intro q _ hq
  have hodd : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : q.Prime).eq_two_or_odd with h | h <;> omega
  have hnz : ∀ n : ℕ, 0 < n → n < q → (n : ZMod q) ≠ 0 := fun n hn0 hnq h => by
    rw [CharP.cast_eq_zero_iff (ZMod q) q] at h
    exact absurd (Nat.le_of_dvd hn0 h) (by omega)
  exact psl2Gen_main (ZMod q) (fun c => ⟨c.val, ZMod.natCast_zmod_val c⟩) hodd
    (by exact_mod_cast hnz 2 (by norm_num) (by omega))
    (by exact_mod_cast hnz 3 (by norm_num) (by omega))
    (by exact_mod_cast hnz 4 (by norm_num) (by omega))

end CFSG.Quasithin.H13.NFa2
