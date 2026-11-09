module

public import CFSG.GH74.KGroups.L27Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.KL27
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L27T

namespace Certificates

private theorem sub2331_le : L27.QP.originalSubgroup ≤ L27.QA.originalSubgroup := by
  rw [L27.QP, L27.QA, CFSG.Sporadic.Schreier.certificate_originalSubgroup,
    CFSG.Sporadic.Schreier.certificate_originalSubgroup]
  apply Subgroup.closure_mono
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg ⊢
  tauto

private theorem norm2331_gen (x : Equiv.Perm (Fin 8)) (hx : x = L27.pa ∨ x = L27.pb) :
    L27.sg0 * x * L27.sg0⁻¹ ∈ L27.QP.originalSubgroup := by
  rw [mem_iff_sift L27.QP L27.QP_ok]
  rcases hx with rfl | rfl
  · rw [eq_ev_cOf L27.sg0, eq_ev_cOf L27.pa]
    simp only [ev_mul', ev_inv', sift_ev]
    exact kNormA
  · rw [eq_ev_cOf L27.sg0, eq_ev_cOf L27.pb]
    simp only [ev_mul', ev_inv', sift_ev]
    exact kNormB

private theorem norm2331_conj (h : Equiv.Perm (Fin 8)) (hh : h ∈ L27.QP.originalSubgroup) :
    L27.sg0 * h * L27.sg0⁻¹ ∈ L27.QP.originalSubgroup := by
  rw [L27.QP_closure] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    exact norm2331_gen x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : L27.sg0 * (x * y) * L27.sg0⁻¹ =
        (L27.sg0 * x * L27.sg0⁻¹) * (L27.sg0 * y * L27.sg0⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have e : L27.sg0 * x⁻¹ * L27.sg0⁻¹ = (L27.sg0 * x * L27.sg0⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihx

private theorem norm2331_le :
    L27.QA.originalSubgroup ≤ Subgroup.normalizer (L27.QP.originalSubgroup : Set _) := by
  rw [L27.QA, CFSG.Sporadic.Schreier.certificate_originalSubgroup, Subgroup.closure_le]
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hs
  rcases hs with rfl | rfl | rfl
  · refine Subgroup.le_normalizer ?_
    rw [L27.QP_closure]
    exact Subgroup.subset_closure (by simp)
  · refine Subgroup.le_normalizer ?_
    rw [L27.QP_closure]
    exact Subgroup.subset_closure (by simp)
  · exact Subgroup.mem_normalizer_fintype norm2331_conj

private theorem inv2331_A : (elemsT L27.QA).all (fun y => !(decide (y * L27.pa = L27.pa * y)) ||
    decide (y ^ 16 = 1)) = true := by
  rw [elemsT_eq_elemsC, eq_ev_cOf L27.pa]
  simp only [List.all_map, Function.comp_def, ev_mul', ev_pow', one_eq_ev, decide_ev_eq]
  exact kInvA

private theorem inv2331_B : (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QP).any fun g => decide (g * L27.pa * g⁻¹ = x)) = true := by
  rw [elemsT_eq_elemsC, eq_ev_cOf L27.pa]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev,
    decide_ev_eq]
  exact kInvB

private theorem inv2331 : (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QA).all fun y => !(decide (y * x = x * y)) || decide (y ^ 16 = 1)) = true := by
  rw [List.all_eq_true]
  intro x hx
  have hBx := List.all_eq_true.1 inv2331_B x hx
  by_cases h1 : x * x = 1
  · by_cases h2 : x = 1
    · simp [h2]
    · simp only [h1, h2, decide_true, decide_false, Bool.not_true, Bool.or_false,
        Bool.false_or] at hBx ⊢
      obtain ⟨g, hg, hgx⟩ := List.any_eq_true.1 hBx
      rw [decide_eq_true_eq] at hgx
      rw [List.all_eq_true]
      intro y hy
      by_cases hc : y * x = x * y
      · have hgA := sub2331_le ((mem_elemsT L27.QP L27.QP_ok g).1 hg)
        have hyA := (mem_elemsT L27.QA L27.QA_ok y).1 hy
        have hz : g⁻¹ * y * g ∈ elemsT L27.QA := (mem_elemsT L27.QA L27.QA_ok _).2
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgA) hyA) hgA)
        have hAz := List.all_eq_true.1 inv2331_A _ hz
        rw [← hgx] at hc
        have hcz : g⁻¹ * y * g * L27.pa = L27.pa * (g⁻¹ * y * g) := by
          have e1 : g⁻¹ * y * g * L27.pa = g⁻¹ * (y * (g * L27.pa * g⁻¹)) * g := by group
          have e2 : L27.pa * (g⁻¹ * y * g) = g⁻¹ * ((g * L27.pa * g⁻¹) * y) * g := by group
          rw [e1, e2, hc]
        simp only [hcz, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hAz
        have ey : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        rw [ey, conj_pow, hAz]
        simp
      · simp [hc]
  · simp [h1]

open CFSG Subgroup CFSG.GH74.KGroups Equiv in
theorem certificate2331 : (
 (elemsT L27.QP).all (fun x => L27.QA.sift x 0) = true 
)
    ∧ (
 (elemsT L27.QA).all
    (fun y => (elemsT L27.QP).all fun x => L27.QP.sift (y * x * y⁻¹) 0) = true 
)
    ∧ (
 (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QA).all fun y => !(decide (y * x = x * y)) || decide (y ^ 16 = 1)) = true 
)
    ∧ (
 ∀ x y : Perm (Fin 5), Perm.sign x = 1 → x * x = 1 → x ≠ 1 →
    y * x = x * y → y ^ 16 = 1 
) := by
  refine ⟨?_, ?_, ?_, kA5Inv⟩
  · rw [List.all_eq_true]
    intro x hx
    rw [← mem_iff_sift L27.QA L27.QA_ok]
    exact sub2331_le ((mem_elemsT L27.QP L27.QP_ok x).1 hx)
  · rw [List.all_eq_true]
    intro y hy
    rw [List.all_eq_true]
    intro x hx
    rw [← mem_iff_sift L27.QP L27.QP_ok]
    have hn := norm2331_le ((mem_elemsT L27.QA L27.QA_ok y).1 hy)
    exact (Subgroup.mem_normalizer_iff.1 hn x).1 ((mem_elemsT L27.QP L27.QP_ok x).1 hx)
  · exact inv2331

end Certificates
