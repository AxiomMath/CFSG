module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.AKN

open Matrix CFSG.SL2MinimalFaithful

variable {F : Type*} [Field F]

@[expose] def dgSL (t : F) (ht : t ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![t, 0; 0, t⁻¹], by simp [det_fin_two_of, ht]⟩

theorem coe_dgSL (t : F) (ht : t ≠ 0) :
    ((dgSL t ht : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![t, 0; 0, t⁻¹] :=
  rfl

theorem dgSL_mul_unipotent (t : F) (ht : t ≠ 0) (c : F) :
    dgSL t ht * unipotent c = unipotent (t ^ 2 * c) * dgSL t ht := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dgSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem dgSL_mul_dgSL_inv (t : F) (ht : t ≠ 0) :
    dgSL t ht * dgSL t⁻¹ (inv_ne_zero ht) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dgSL, Matrix.mul_apply, Fin.sum_univ_two, ht]

theorem entry_one_zero_of_comm {g : SpecialLinearGroup (Fin 2) F} {e : F}
    (h : g * unipotent 1 = unipotent e * g) : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] at h1
  linear_combination h1

theorem eq_unipotent_mul_dgSL {g : SpecialLinearGroup (Fin 2) F}
    (h : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0) :
    g = unipotent ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1) *
      dgSL _ h0 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [det_fin_two, h, mul_zero, sub_zero] at hdet
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = ((g : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dgSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, h, h11]
  field_simp

variable [CharP F 2]

theorem eq_of_sq_eq_sq {a b : F} (h : a ^ 2 = b ^ 2) : a = b := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (a - b) ^ 2 = 0 := by linear_combination h + (b ^ 2 - a * b) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

@[expose] def wSL : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two_of, CharTwo.neg_eq]⟩

theorem coe_wSL :
    ((wSL : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] :=
  rfl

theorem wSL_mul_dgSL (t : F) (ht : t ≠ 0) :
    wSL * dgSL t ht = dgSL t⁻¹ (inv_ne_zero ht) * wSL := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dgSL, coe_wSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_wSL_rel :
    unipotent (1 : F) * wSL * unipotent 1 * wSL * unipotent 1 = wSL := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_wSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem unipotent_mul_self (c : F) : unipotent c * unipotent c = 1 := by
  rw [← unipotent_add, show c + c = 0 by rw [← two_mul, CharTwo.two_eq_zero, zero_mul],
    unipotent_zero]

theorem antidiag_of_conj {g : SpecialLinearGroup (Fin 2) F} {t : F} (ht : t ≠ 0) (ht1 : t ≠ 1)
    (h : g * dgSL t ht = dgSL t⁻¹ (inv_ne_zero ht) * g) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hne : t - t⁻¹ ≠ 0 := by
    intro h0
    have h1 : t * t = 1 := by
      have := congrArg (· * t) h0
      simp only [sub_mul, inv_mul_cancel₀ ht, zero_mul] at this
      linear_combination this
    exact ht1 (eq_of_sq_eq_sq (by rw [sq, h1, one_pow]))
  have e0 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [coe_dgSL, Matrix.mul_apply, Fin.sum_univ_two] at e0 e1
  refine ⟨(mul_eq_zero.mp (show (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (t - t⁻¹) = 0 by
    linear_combination e0)).resolve_right hne, (mul_eq_zero.mp
    (show (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (t - t⁻¹) = 0 by
      linear_combination -e1)).resolve_right hne⟩

theorem eq_wSL_of_rel {g : SpecialLinearGroup (Fin 2) F}
    (h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (h1 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (h : unipotent 1 * g * unipotent 1 * g * unipotent 1 = g) : g = wSL := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [det_fin_two, h0, h1, zero_mul, zero_sub] at hdet
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  have hbc : b * c = 1 := by linear_combination -hdet - h2
  have hc0 : c ≠ 0 := by
    rintro hc'
    rw [hc', mul_zero] at hbc
    exact zero_ne_one hbc
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![0, b; c, 0] := by
    rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) F), h0, h1]
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, hg, Matrix.mul_fin_two] at hm
  have e10 := congrFun (congrFun hm 1) 0
  have e00 := congrFun (congrFun hm 0) 0
  simp at e10 e00
  have hc1 : c = 1 := by
    have : c * (c - 1) = 0 := by linear_combination e10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
  have hb1 : b = 1 := by
    rw [hc1, mul_one] at hbc
    exact hbc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wSL, h0, h1, ← hb, ← hc, hb1, hc1]

theorem wSL_mul_unipotent_mul_wSL (c : F) :
    ((wSL * unipotent c * wSL : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_wSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_unipotent_of_comm {g : SpecialLinearGroup (Fin 2) F}
    (h : g * unipotent 1 = unipotent 1 * g) :
    g = unipotent ((g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h10 := entry_one_zero_of_comm h
  have h01 := congrArg
    (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [det_fin_two, h10, mul_zero, sub_zero] at hdet
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_of_sq_eq_sq
    rw [one_pow, sq]
    nth_rewrite 2 [show (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1 by
      linear_combination h01]
    exact hdet
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by linear_combination -h01 + h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipotent, h00, h10, h11]

theorem exists_eq_conj_of_fix [Finite F] (hF : 2 < Nat.card F)
    (α : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F)
    (hα : ∀ c, α (unipotent c) = unipotent c) :
    ∃ c₀ : F, ∀ g, α g = unipotent c₀ * g * (unipotent c₀)⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
    classical
    by_contra hall
    push Not at hall
    have := Fintype.ofFinite F
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hall x hx]
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
    have h4 := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  have hsq : 1 + t₀ ^ 2 ≠ 0 := by
    intro h
    apply ht₀1
    exact eq_of_sq_eq_sq (by linear_combination h - h2)
  set g₀ := α (dgSL t₀ ht₀) with hg₀
  have hg₀u : g₀ * unipotent 1 = unipotent (t₀ ^ 2) * g₀ := by
    have := congrArg α (dgSL_mul_unipotent t₀ ht₀ 1)
    rwa [map_mul, map_mul, hα, hα, mul_one] at this
  have h10 := entry_one_zero_of_comm hg₀u
  have h01 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1)
    hg₀u
  simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hdet := Matrix.SpecialLinearGroup.det_coe g₀
  rw [det_fin_two, h10, mul_zero, sub_zero] at hdet
  have ha : (g₀ : Matrix (Fin 2) (Fin 2) F) 0 0 = t₀ := by
    apply eq_of_sq_eq_sq
    linear_combination (g₀ : Matrix (Fin 2) (Fin 2) F) 0 0 * h01 + t₀ ^ 2 * hdet
  have ha0 : (g₀ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by rw [ha]; exact ht₀
  have hg₀eq := eq_unipotent_mul_dgSL h10 ha0
  set x := (g₀ : Matrix (Fin 2) (Fin 2) F) 0 0 * (g₀ : Matrix (Fin 2) (Fin 2) F) 0 1 with hx
  have hg₀' : g₀ = unipotent x * dgSL t₀ ht₀ := by
    rw [hg₀eq]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_dgSL, ha]
  set c₀ := x / (1 + t₀ ^ 2) with hc₀
  have hu0 : (unipotent c₀)⁻¹ = unipotent c₀ := inv_eq_of_mul_eq_one_right (unipotent_mul_self c₀)
  have hconj : unipotent c₀ * dgSL t₀ ht₀ * (unipotent c₀)⁻¹ = unipotent x * dgSL t₀ ht₀ := by
    rw [hu0, mul_assoc, dgSL_mul_unipotent, ← mul_assoc, ← unipotent_add]
    congr 2
    rw [hc₀]
    field_simp
  obtain ⟨α', hα'apply⟩ : ∃ α' : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F,
      ∀ g, α' g = (unipotent c₀)⁻¹ * α g * unipotent c₀ :=
    ⟨(MulAut.conj (unipotent c₀)⁻¹).toMonoidHom.comp α, fun g => by simp⟩
  have hα'u : ∀ c, α' (unipotent c) = unipotent c := fun c => by
    rw [hα'apply, hα, hu0, mul_assoc, ← unipotent_add, ← unipotent_add, add_comm, add_assoc,
      show c₀ + c₀ = 0 by rw [← two_mul, h2, zero_mul], add_zero]
  have hα'd : α' (dgSL t₀ ht₀) = dgSL t₀ ht₀ := by
    rw [hα'apply, ← hg₀, hg₀', ← hconj]
    group
  have hα'dinv : α' (dgSL t₀⁻¹ (inv_ne_zero ht₀)) = dgSL t₀⁻¹ (inv_ne_zero ht₀) := by
    have e := dgSL_mul_dgSL_inv t₀ ht₀
    have e1 : dgSL t₀⁻¹ (inv_ne_zero ht₀) = (dgSL t₀ ht₀)⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [e1, map_inv, hα'd]
  have hw0 : α' wSL * dgSL t₀ ht₀ = dgSL t₀⁻¹ (inv_ne_zero ht₀) * α' wSL := by
    have := congrArg α' (wSL_mul_dgSL t₀ ht₀)
    rwa [map_mul, map_mul, hα'd, hα'dinv] at this
  obtain ⟨hw00, hw11⟩ := antidiag_of_conj ht₀ ht₀1 hw0
  have hwrel : unipotent 1 * α' wSL * unipotent 1 * α' wSL * unipotent 1 = α' wSL := by
    have := congrArg α' (unipotent_wSL_rel (F := F))
    rwa [map_mul, map_mul, map_mul, map_mul, hα'u] at this
  have hα'w : α' wSL = wSL := eq_wSL_of_rel hw00 hw11 hwrel
  have hfix : ∀ g, α' g = g := by
    intro g
    refine Matrix.SL2.transvection_induction (fun g => α' g = g) ?_ ?_ g
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · have e : SpecialLinearGroup.transvection hij c = unipotent c := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [SpecialLinearGroup.transvection_coe, coe_unipotent, one_apply]
        rw [e, hα'u]
      · have e : SpecialLinearGroup.transvection hij c = wSL * unipotent c * wSL := by
          ext a b
          rw [wSL_mul_unipotent_mul_wSL]
          fin_cases a <;> fin_cases b <;>
            simp [SpecialLinearGroup.transvection_coe, one_apply]
        rw [e, map_mul, map_mul, hα'w, hα'u]
      · exact absurd rfl hij
    · intro A B hA hB
      rw [map_mul, hA, hB]
  refine ⟨c₀, fun g => ?_⟩
  have := hfix g
  rw [hα'apply] at this
  calc α g = unipotent c₀ * ((unipotent c₀)⁻¹ * α g * unipotent c₀) * (unipotent c₀)⁻¹ := by
        group
    _ = unipotent c₀ * g * (unipotent c₀)⁻¹ := by rw [this]

end CFSG.Quasithin.Vol2.Ch11.SecA.AKN
