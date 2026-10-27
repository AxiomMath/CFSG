module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.NaturalCover
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF3

public section

namespace CFSG.Quasithin

open Matrix

namespace Stellmacher.PU.L3YC

section Bil

variable {F : Type} [Field F] [Fintype F]

theorem tvGL_mulVec_single (i j a : Fin 3) (h : i ≠ j) :
    ((CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL i j h (1 : F) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec (Pi.single a 1) =
      Pi.single a 1 + (if a = j then Pi.single i 1 else 0) := by
  rw [CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL_val]
  ext m
  by_cases ha : a = j <;> by_cases hm : m = i <;> simp [transvection, Matrix.mulVec, dotProduct,
    Pi.single_apply, Matrix.one_apply, Matrix.single_apply, ha, hm, h]
  all_goals (first | omega | aesop)

theorem tvGL_mulVec (i j : Fin 3) (h : i ≠ j) (w : Fin 3 → F) :
    ((CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL i j h (1 : F) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec w = w + Pi.single i (w j) := by
  rw [CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL_val]
  ext m
  fin_cases i <;> fin_cases j <;> fin_cases m <;> first | exact absurd rfl h | (simp [transvection,
    Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.sum_univ_three] <;> ring)

theorem tvGL_inv_mulVec_transpose (hneg : (-1 : F) = 1) (i j b : Fin 3) (h : i ≠ j) :
    ((((CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL i j h (1 : F))⁻¹ :
        Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).mulVec (Pi.single b 1) =
      Pi.single b 1 + (if b = i then Pi.single j 1 else 0) := by
  rw [CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL_inv_val, hneg]
  ext m
  fin_cases i <;> fin_cases j <;> fin_cases b <;> fin_cases m <;> first | exact absurd rfl h |
    (simp [transvection, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;> ring)

theorem bil_key (hneg : (-1 : F) = 1)
    (B : (Fin 3 → F) →+ (Fin 3 → F) →+ (Fin 3 → F))
    (hB : ∀ (g : Matrix.GeneralLinearGroup (Fin 3) F) (v f : Fin 3 → F),
      B ((g : Matrix (Fin 3) (Fin 3) F).mulVec v)
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ.mulVec f) =
        (g : Matrix (Fin 3) (Fin 3) F).mulVec (B v f))
    (i j : Fin 3) (h : i ≠ j) (a b : Fin 3) :
    (if a = j then B (Pi.single i 1) (Pi.single b 1) else 0) +
      (if b = i then B (Pi.single a 1) (Pi.single j 1) else 0) +
      (if a = j ∧ b = i then B (Pi.single i 1) (Pi.single j 1) else 0) =
      Pi.single i ((B (Pi.single a 1) (Pi.single b 1)) j) := by
  have e := hB (CFSG.Quasithin.Stellmacher.CD.L3YC.tvGL i j h (1 : F)) (Pi.single a 1) (Pi.single b 1)
  rw [tvGL_mulVec_single i j a h, tvGL_inv_mulVec_transpose hneg i j b h, tvGL_mulVec] at e
  by_cases ha : a = j <;> by_cases hb : b = i <;> simp only [ha, hb, ite_true, ite_false, and_self,
    true_and, and_true, and_false, false_and, add_zero, map_add, AddMonoidHom.add_apply,
    map_zero, AddMonoidHom.zero_apply, zero_add] at e ⊢ <;>
  exact sub_eq_zero.mp (by have h0 := sub_eq_zero.mpr e; abel_nf at h0 ⊢; exact h0)

@[expose] def xv (B : (Fin 3 → F) →+ (Fin 3 → F) →+ (Fin 3 → F)) (a b k : Fin 3) : F :=
  B (Pi.single a 1) (Pi.single b 1) k

theorem bil_comp (hneg : (-1 : F) = 1)
    (B : (Fin 3 → F) →+ (Fin 3 → F) →+ (Fin 3 → F))
    (hB : ∀ (g : Matrix.GeneralLinearGroup (Fin 3) F) (v f : Fin 3 → F),
      B ((g : Matrix (Fin 3) (Fin 3) F).mulVec v)
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ.mulVec f) =
        (g : Matrix (Fin 3) (Fin 3) F).mulVec (B v f))
    (i j : Fin 3) (h : i ≠ j) (a b k : Fin 3) :
    (if a = j then xv B i b k else 0) + (if b = i then xv B a j k else 0) +
      (if a = j ∧ b = i then xv B i j k else 0) = (if k = i then xv B a b j else 0) := by
  have e := congrFun (bil_key hneg B hB i j h a b) k
  by_cases ha : a = j <;> by_cases hb : b = i <;> by_cases hk : k = i <;>
    simp [xv, ha, hb, hk, Pi.single_apply] at e ⊢ <;> exact e

theorem bil_zero (hF : Fintype.card F = 2)
    (B : (Fin 3 → F) →+ (Fin 3 → F) →+ (Fin 3 → F))
    (hB : ∀ (g : Matrix.GeneralLinearGroup (Fin 3) F) (v f : Fin 3 → F),
      B ((g : Matrix (Fin 3) (Fin 3) F).mulVec v)
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ.mulVec f) =
        (g : Matrix (Fin 3) (Fin 3) F).mulVec (B v f)) (v f : Fin 3 → F) : B v f = 0 := by
  have h2 : (2 : F) = 0 := by
    rcases eq_zero_or_one_of_card_two hF ((1 : F) + 1) with h | h
    · rw [← one_add_one_eq_two]; exact h
    · exact absurd (add_eq_right.mp h) one_ne_zero
  have hneg : (-1 : F) = 1 := by linear_combination (-1 : F) * h2
  have E0 := bil_comp hneg B hB 0 1 (by decide) 0 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E0
  have E1 := bil_comp hneg B hB 0 1 (by decide) 0 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E1
  have E2 := bil_comp hneg B hB 0 1 (by decide) 0 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E2
  have E4 := bil_comp hneg B hB 0 1 (by decide) 0 2 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E4
  have E5 := bil_comp hneg B hB 0 1 (by decide) 1 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E5
  have E6 := bil_comp hneg B hB 0 1 (by decide) 1 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E6
  have E7 := bil_comp hneg B hB 0 1 (by decide) 1 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E7
  have E11 := bil_comp hneg B hB 0 1 (by decide) 1 2 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E11
  have E13 := bil_comp hneg B hB 0 1 (by decide) 1 2 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E13
  have E14 := bil_comp hneg B hB 0 1 (by decide) 2 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E14
  have E15 := bil_comp hneg B hB 0 1 (by decide) 2 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E15
  have E16 := bil_comp hneg B hB 0 1 (by decide) 2 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E16
  have E18 := bil_comp hneg B hB 0 1 (by decide) 2 2 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E18
  have E19 := bil_comp hneg B hB 0 2 (by decide) 0 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E19
  have E24 := bil_comp hneg B hB 0 2 (by decide) 1 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E24
  have E25 := bil_comp hneg B hB 0 2 (by decide) 1 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E25
  have E26 := bil_comp hneg B hB 0 2 (by decide) 1 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E26
  have E29 := bil_comp hneg B hB 0 2 (by decide) 2 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E29
  have E30 := bil_comp hneg B hB 0 2 (by decide) 2 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E30
  have E31 := bil_comp hneg B hB 0 2 (by decide) 2 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E31
  have E38 := bil_comp hneg B hB 1 0 (by decide) 0 0 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E38
  have E39 := bil_comp hneg B hB 1 0 (by decide) 0 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E39
  have E40 := bil_comp hneg B hB 1 0 (by decide) 0 0 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E40
  have E41 := bil_comp hneg B hB 1 0 (by decide) 0 1 0
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E41
  have E52 := bil_comp hneg B hB 1 0 (by decide) 2 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E52
  have E55 := bil_comp hneg B hB 1 0 (by decide) 2 1 2
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E55
  have E77 := bil_comp hneg B hB 2 0 (by decide) 0 0 1
  simp only [Fin.reduceEq, ite_true, ite_false, and_true, true_and, and_false, false_and, and_self, add_zero, zero_add] at E77
  have X0 : xv B 0 0 0 = 0 := by linear_combination E0 + E4 + E5 + E18 + E30 + E38 + E39 + E41 + (-1) * (xv B 0 1 0) * h2 + (-1) * (xv B 1 0 0) * h2 + (-1) * (xv B 1 1 0) * h2
  have X1 : xv B 0 0 1 = 0 := by linear_combination E4 + E18 + E30
  have X2 : xv B 0 0 2 = 0 := by linear_combination E11 + E19 + E25 + (1) * (xv B 0 0 2) * h2 + (-1) * (xv B 0 2 0) * h2
  have X3 : xv B 0 1 0 = 0 := by linear_combination E0 + E4 + E18 + E30
  have X4 : xv B 0 1 1 = 0 := by linear_combination E1
  have X5 : xv B 0 1 2 = 0 := by linear_combination E2
  have X6 : xv B 0 2 0 = 0 := by linear_combination E11 + E25
  have X7 : xv B 0 2 1 = 0 := by linear_combination E4 + (1) * (xv B 0 2 1) * h2
  have X8 : xv B 0 2 2 = 0 := by linear_combination E13
  have X9 : xv B 1 0 0 = 0 := by linear_combination E38
  have X10 : xv B 1 0 1 = 0 := by linear_combination E0 + E4 + E5 + E18 + E30 + E38 + E41 + (-1) * (xv B 0 0 0) * h2 + (-1) * (xv B 0 1 0) * h2 + (-1) * (xv B 1 0 0) * h2 + (1) * (xv B 1 0 1) * h2 + (-1) * (xv B 1 1 0) * h2
  have X11 : xv B 1 0 2 = 0 := by linear_combination E40
  have X12 : xv B 1 1 0 = 0 := by linear_combination E0 + E4 + E5 + E18 + E30 + E39 + (-1) * (xv B 0 1 0) * h2
  have X13 : xv B 1 1 1 = 0 := by linear_combination E1 + E4 + E6 + E18 + E30 + (-1) * (xv B 0 0 1) * h2 + (-1) * (xv B 0 1 1) * h2
  have X14 : xv B 1 1 2 = 0 := by linear_combination E2 + E7 + E11 + E19 + E25 + (-1) * (xv B 0 1 2) * h2 + (-1) * (xv B 0 2 0) * h2
  have X15 : xv B 1 2 0 = 0 := by linear_combination E24 + E40
  have X16 : xv B 1 2 1 = 0 := by linear_combination E25
  have X17 : xv B 1 2 2 = 0 := by linear_combination E26
  have X18 : xv B 2 0 0 = 0 := by linear_combination E52 + (1) * (xv B 2 0 0) * h2
  have X19 : xv B 2 0 1 = 0 := by linear_combination E77
  have X20 : xv B 2 0 2 = 0 := by linear_combination E55
  have X21 : xv B 2 1 0 = 0 := by linear_combination E14 + E77
  have X22 : xv B 2 1 1 = 0 := by linear_combination E15
  have X23 : xv B 2 1 2 = 0 := by linear_combination E16
  have X24 : xv B 2 2 0 = 0 := by linear_combination E0 + E4 + E5 + E11 + E18 + E25 + E29 + E30 + E38 + E39 + E41 + E55 + (-1) * (xv B 0 0 0) * h2 + (-1) * (xv B 0 1 0) * h2 + (-1) * (xv B 0 2 0) * h2 + (-1) * (xv B 1 0 0) * h2 + (-1) * (xv B 1 1 0) * h2
  have X25 : xv B 2 2 1 = 0 := by linear_combination E18 + (1) * (xv B 2 2 1) * h2
  have X26 : xv B 2 2 2 = 0 := by linear_combination E11 + E13 + E19 + E25 + E31 + (-1) * (xv B 0 2 0) * h2 + (-1) * (xv B 0 2 2) * h2
  have hz : ∀ a b : Fin 3, B (Pi.single a 1) (Pi.single b 1) = 0 := by
    intro a b
    funext k
    have : xv B a b k = 0 := by
      fin_cases a <;> fin_cases b <;> fin_cases k <;> assumption
    exact this
  have hs : ∀ (a : Fin 3) (c : F), c = 0 ∨ c = 1 → ∀ f : Fin 3 → F, ∀ b : Fin 3,
      B (Pi.single a c) (Pi.single b 1) = 0 := by
    intro a c hc f b
    rcases hc with rfl | rfl
    · simp
    · exact hz a b
  have hs2 : ∀ (a b : Fin 3) (c d : F), c = 0 ∨ c = 1 → d = 0 ∨ d = 1 →
      B (Pi.single a c) (Pi.single b d) = 0 := by
    intro a b c d hc hd
    rcases hd with rfl | rfl
    · simp
    · exact hs a c hc 0 b
  have hv : v = ∑ a, Pi.single a (v a) := by
    ext m; simp [Finset.sum_apply, Pi.single_apply]
  have hf : f = ∑ b, Pi.single b (f b) := by
    ext m; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, hf]
  simp only [map_sum, AddMonoidHom.finset_sum_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  first
  | (have := hs2 a b (v a) (f b) (eq_zero_or_one_of_card_two hF _)
      (eq_zero_or_one_of_card_two hF _); simpa using this)
  | (have := hs2 b a (v b) (f a) (eq_zero_or_one_of_card_two hF _)
      (eq_zero_or_one_of_card_two hF _); simpa using this)

end Bil

end Stellmacher.PU.L3YC

end CFSG.Quasithin
