module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.H13.AS91

open Matrix

section Elem8

private theorem exists_gl_transvection {u v : Fin 3 → ZMod 2} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) :
    ∃ M : GL (Fin 3) (ZMod 2), (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u = u ∧
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v + u := by
  have key : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 → u ≠ v →
      ∃ c : Fin 3 → ZMod 2, dotProduct c u = 0 ∧ dotProduct c v = 1 := by
    decide
  have inv : ∀ u c : Fin 3 → ZMod 2, dotProduct c u = 0 →
      (1 + vecMulVec u c) * (1 + vecMulVec u c) = 1 := by
    decide
  obtain ⟨c, hcu, hcv⟩ := key u v hu hv huv
  refine ⟨⟨1 + vecMulVec u c, 1 + vecMulVec u c, inv u c hcu, inv u c hcu⟩, ?_, ?_⟩
  · simp [add_mulVec, vecMulVec_mulVec, hcu]
  · simp [add_mulVec, vecMulVec_mulVec, hcv]

private theorem zmod2_add_add_self (x y : Fin 3 → ZMod 2) : x + (x + y) = y := by
  funext i
  have h : ∀ a b : ZMod 2, a + (a + b) = b := by decide
  exact h (x i) (y i)

private theorem toAdd_eq_zero_iff_of_mulEquiv {Z : Type*} [Group Z]
    (e : Z ≃* Multiplicative (Fin 3 → ZMod 2)) (g : Z) :
    Multiplicative.toAdd (e g) = 0 ↔ g = 1 := by
  rw [toAdd_eq_zero, map_eq_one_iff e e.injective]

private theorem eq_of_mul_eq_one_of_sq {Z : Type*} [Group Z] (hsq : ∀ a : Z, a * a = 1)
    {a b : Z} (h : a * b = 1) : a = b :=
  (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right (hsq b))

variable {Z : Type*} [Group Z]

theorem elem8_card_mulAut_le [Finite Z] (hcomm : ∀ a b : Z, a * b = b * a)
    (hsq : ∀ a : Z, a * a = 1) (hcard : Nat.card Z = 8) : Nat.card (MulAut Z) ≤ 168 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun a => by rw [pow_two]; exact hsq a) (n := 3) (hcard.trans (by norm_num))
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 3]
  norm_num [Fin.prod_univ_three]

theorem elem8_exists_mulAut_apply_eq [Finite Z] (hcomm : ∀ a b : Z, a * b = b * a)
    (hsq : ∀ a : Z, a * a = 1) (hcard : Nat.card Z = 8) {a b : Z} (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ f : MulAut Z, f a = b := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun x => by rw [pow_two]; exact hsq x) (n := 3) (hcard.trans (by norm_num))
  by_cases hab : a = b
  · exact ⟨1, by simp [hab]⟩
  have hx : Multiplicative.toAdd (e a) ≠ 0 :=
    fun h => ha ((toAdd_eq_zero_iff_of_mulEquiv e a).1 h)
  have hxy : Multiplicative.toAdd (e a) + Multiplicative.toAdd (e b) ≠ 0 := by
    intro h
    rw [← toAdd_mul, ← map_mul] at h
    exact hab (eq_of_mul_eq_one_of_sq hsq ((toAdd_eq_zero_iff_of_mulEquiv e _).1 h))
  have hxy' : Multiplicative.toAdd (e a) + Multiplicative.toAdd (e b) ≠
      Multiplicative.toAdd (e a) := by
    intro h
    have h0 := add_left_cancel (h.trans (add_zero _).symm)
    exact hb ((toAdd_eq_zero_iff_of_mulEquiv e b).1 h0)
  obtain ⟨M, -, hMv⟩ := exists_gl_transvection hxy hx hxy'
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm M, ?_⟩
  have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm M) a
  rw [MulEquiv.apply_symm_apply, hMv, zmod2_add_add_self] at h1
  apply e.injective
  apply Multiplicative.toAdd.injective
  exact h1.symm

theorem elem8_exists_mulAut_fix [Finite Z] (hcomm : ∀ a b : Z, a * b = b * a)
    (hsq : ∀ a : Z, a * a = 1) (hcard : Nat.card Z = 8) {z w : Z} (hz : z ≠ 1) (hw : w ≠ 1)
    (hwz : w ≠ z) : ∃ f : MulAut Z, f z = z ∧ f w ≠ w := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun x => by rw [pow_two]; exact hsq x) (n := 3) (hcard.trans (by norm_num))
  have hz' : Multiplicative.toAdd (e z) ≠ 0 :=
    fun h => hz ((toAdd_eq_zero_iff_of_mulEquiv e z).1 h)
  have hw' : Multiplicative.toAdd (e w) ≠ 0 :=
    fun h => hw ((toAdd_eq_zero_iff_of_mulEquiv e w).1 h)
  have hzw : Multiplicative.toAdd (e z) ≠ Multiplicative.toAdd (e w) :=
    fun h => hwz (e.injective (Multiplicative.toAdd.injective h)).symm
  obtain ⟨M, hMz, hMw⟩ := exists_gl_transvection hz' hw' hzw
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm M, ?_, ?_⟩
  · have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm M) z
    rw [MulEquiv.apply_symm_apply, hMz] at h1
    exact e.injective (Multiplicative.toAdd.injective h1.symm)
  · intro h
    have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm M) w
    rw [MulEquiv.apply_symm_apply, hMw, h] at h1
    exact hz' (add_left_cancel (h1.trans (add_zero _).symm))

end Elem8

end CFSG.Quasithin.H13.AS91
