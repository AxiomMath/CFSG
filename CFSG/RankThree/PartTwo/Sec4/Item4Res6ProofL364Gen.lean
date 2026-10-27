module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherRigidity
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

noncomputable abbrev tv {i j : Fin 3} (h : i ≠ j) (c : K64) : SpecialLinearGroup (Fin 3) K64 :=
  SpecialLinearGroup.transvection h c

theorem tv_mul {i j : Fin 3} (h : i ≠ j) (c d : K64) : tv h c * tv h d = tv h (c + d) := by
  apply Subtype.ext
  exact Matrix.transvection_mul_transvection_same i j h c d

theorem tv_zero {i j : Fin 3} (h : i ≠ j) : tv h 0 = 1 :=
  SpecialLinearGroup.transvection_coeff_zero h

theorem diag_mul_transvection {D : SpecialLinearGroup (Fin 3) K64} {d : Fin 3 → K64}
    (hD : (D : Matrix (Fin 3) (Fin 3) K64) = diagonal d) {i j : Fin 3} (h : i ≠ j) (c : K64)
    (hdj : d j ≠ 0) : D * tv h c = tv h (d i * c / d j) * D := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, hD]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.single_apply]
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    field_simp
  · simp

@[expose] noncomputable def wK : Matrix (Fin 3) (Fin 3) K64 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem wK_apply (a b : Fin 3) : wK a b = if a = b + 1 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

theorem det_wK : wK.det = 1 := by
  rw [Matrix.det_fin_three]
  simp [wK]

@[expose] noncomputable def wSL : SpecialLinearGroup (Fin 3) K64 := ⟨wK, det_wK⟩

theorem coe_wSL : (wSL : Matrix (Fin 3) (Fin 3) K64) = wK := rfl

theorem w_mul_transvection {i j : Fin 3} (h : i ≠ j) (c : K64) :
    wSL * tv h c = tv (by simpa using h : i + 1 ≠ j + 1) c * wSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, coe_wSL]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, wK_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all

theorem eq_top_of_transvections {H : Subgroup (SpecialLinearGroup (Fin 3) K64)}
    (hH : ∀ (i j : Fin 3) (h : i ≠ j) (c : K64), tv h c ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := K64),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact hH i j hij c

theorem forall_tv_mem {H : Subgroup (SpecialLinearGroup (Fin 3) K64)} {i j : Fin 3} (h : i ≠ j)
    {c₀ : K64} (hc₀ : c₀ ≠ 0) (h₀ : tv h c₀ ∈ H) {Z T : SpecialLinearGroup (Fin 3) K64}
    {z t : Fin 3 → K64} (hZ : (Z : Matrix (Fin 3) (Fin 3) K64) = diagonal z)
    (hT : (T : Matrix (Fin 3) (Fin 3) K64) = diagonal t) (hZH : Z ∈ H) (hTH : T ∈ H)
    (hzj : z j ≠ 0) (htj : t j ≠ 0) (hζ : (z i / z j) ^ 2 + z i / z j + 1 = 0)
    (hβ7 : (t i / t j) ^ 7 = 1) (hβ1 : t i / t j ≠ 1) (c : K64) : tv h c ∈ H := by
  let A : AddSubgroup K64 :=
    { carrier := {c | tv h c ∈ H}
      add_mem' := fun {a b} ha hb => by
        show tv h (a + b) ∈ H
        rw [← tv_mul]; exact H.mul_mem ha hb
      zero_mem' := by show tv h 0 ∈ H; rw [tv_zero]; exact H.one_mem
      neg_mem' := fun {a} ha => by
        show tv h (-a) ∈ H
        have : tv h (-a) = (tv h a)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, tv_mul, neg_add_cancel, tv_zero]
        rw [this]; exact H.inv_mem ha }
  have hconj : ∀ {D : SpecialLinearGroup (Fin 3) K64} {d : Fin 3 → K64},
      (D : Matrix (Fin 3) (Fin 3) K64) = diagonal d → D ∈ H → d j ≠ 0 →
      ∀ x ∈ A, d i / d j * x ∈ A := by
    intro D d hD hDH hdj x hx
    show tv h (d i / d j * x) ∈ H
    have e := diag_mul_transvection hD h x hdj
    have : tv h (d i / d j * x) = D * tv h x * D⁻¹ := by
      rw [e, mul_inv_cancel_right]; congr 1; ring
    rw [this]
    exact H.mul_mem (H.mul_mem hDH hx) (H.inv_mem hDH)
  have hgen : ∀ x ∈ AddSubgroup.closure (gensSet (z i / z j) (t i / t j)), x * c₀ ∈ A := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rw [gensSet, Set.mem_ofPred_eq] at hx
      obtain ⟨a, e, rfl⟩ := hx
      induction a with
      | zero =>
        induction e with
        | zero =>
          have e1 : (z i / z j) ^ 0 * (t i / t j) ^ 0 * c₀ = c₀ := by simp
          rw [e1]; exact h₀
        | succ e ih =>
          have := hconj hT hTH htj _ ih
          rw [pow_succ]
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
      | succ a ih =>
        have := hconj hZ hZH hzj _ ih
        rw [pow_succ]
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
    | zero => rw [zero_mul]; exact A.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact A.add_mem hx hy
    | neg x _ hx => rw [neg_mul]; exact A.neg_mem hx
  have htop := closure_gensSet_eq_top hζ hβ7 hβ1
  have := hgen (c / c₀) (by rw [htop]; trivial)
  rwa [div_mul_cancel₀ c hc₀] at this

theorem eq_top_of_orbits {H : Subgroup (SpecialLinearGroup (Fin 3) K64)} (hw : wSL ∈ H)
    (h20 : ∀ c, tv (by decide : (2 : Fin 3) ≠ 0) c ∈ H)
    (h10 : ∀ c, tv (by decide : (1 : Fin 3) ≠ 0) c ∈ H) : H = ⊤ := by
  have hstep : ∀ {i j : Fin 3} (h : i ≠ j), (∀ c, tv h c ∈ H) →
      ∀ c, tv (by simpa using h : i + 1 ≠ j + 1) c ∈ H := by
    intro i j h hall c
    have e := w_mul_transvection h c
    have : tv (by simpa using h : i + 1 ≠ j + 1) c = wSL * tv h c * wSL⁻¹ := by
      rw [e, mul_inv_cancel_right]
    rw [this]
    exact H.mul_mem (H.mul_mem hw (hall c)) (H.inv_mem hw)
  have h01 := hstep _ h20
  have h12 := hstep _ h01
  have h21 := hstep _ h10
  have h02 := hstep _ h21
  apply eq_top_of_transvections
  intro i j hij c
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · exact h20 c
  · exact h21 c
  · exact absurd rfl hij

end CFSG.RankThree.PartTwo.Sec4.Res6L364
