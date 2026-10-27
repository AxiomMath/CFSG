module

public import CFSG.Quasithin.Vol2.Ch12Sec5Aut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Quasithin S125 S125ZV S125Aut Matrix

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125W

@[expose] def CoordFix (S : Finset (Fin 10)) (M : Matrix (Fin 10) (Fin 10) (ZMod 2)) : Prop :=
  ∀ l ∈ S, ∀ k ∉ S, M k l = 0

theorem mulVec_vanish {S : Finset (Fin 10)} {M : Matrix (Fin 10) (Fin 10) (ZMod 2)}
    (hM : CoordFix S M) {x : Fin 10 → ZMod 2} (hx : ∀ k ∉ S, x k = 0) :
    ∀ k ∉ S, (M *ᵥ x) k = 0 := by
  intro k hk
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l ∈ S
  · rw [hM l hl k hk, zero_mul]
  · rw [hx l hl, mul_zero]

theorem coordFix_of_mulVec {S : Finset (Fin 10)} {M : Matrix (Fin 10) (Fin 10) (ZMod 2)}
    (h : ∀ x : Fin 10 → ZMod 2, (∀ k ∉ S, x k = 0) → ∀ k ∉ S, (M *ᵥ x) k = 0) :
    CoordFix S M := by
  intro l hl k hk
  have h1 := h (Pi.single l 1) (fun k' hk' => Pi.single_eq_of_ne (by rintro rfl; exact hk' hl) _)
    k hk
  rw [Matrix.mulVec_single] at h1
  simpa using h1

theorem coordFix_iff_mulVec {S : Finset (Fin 10)} {M : Matrix (Fin 10) (Fin 10) (ZMod 2)} :
    CoordFix S M ↔
      ∀ x : Fin 10 → ZMod 2, (∀ k ∉ S, x k = 0) → ∀ k ∉ S, (M *ᵥ x) k = 0 :=
  ⟨fun hM _ hx => mulVec_vanish hM hx, coordFix_of_mulVec⟩

theorem coordFix_transpose {S : Finset (Fin 10)} {M : Matrix (Fin 10) (Fin 10) (ZMod 2)} :
    CoordFix S M ↔ CoordFix Sᶜ Mᵀ := by
  constructor
  · intro h l hl k hk
    rw [Finset.mem_compl, not_not] at hk
    exact h k hk l (Finset.mem_compl.1 hl)
  · intro h l hl k hk
    have := h k (Finset.mem_compl.2 hk) l (by rw [Finset.mem_compl, not_not]; exact hl)
    exact this

theorem wedgeMat_transpose (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    JonesParshall.wedgeMat gᵀ = (JonesParshall.wedgeMat g)ᵀ := by
  ext k l
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, Matrix.transpose_apply]
  ring

theorem wedgeMat_mulVec_single_ne (g : SL5) (l : Fin 10) :
    JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single l 1 ≠ 0 := by
  intro h
  have h1 := wedgeRep_inv_apply g (Pi.single l 1)
  rw [wedgeRep_apply g, h, map_zero] at h1
  have h2 := congrFun h1 l
  simp at h2

@[expose] def minor (x y : Fin 5 → ZMod 2) (p : Fin 10) : ZMod 2 :=
  x (JonesParshall.pr5 p).1 * y (JonesParshall.pr5 p).2 -
    x (JonesParshall.pr5 p).2 * y (JonesParshall.pr5 p).1

@[expose] def pairsIn (A : Finset (Fin 5)) : Finset (Fin 10) :=
  Finset.univ.filter fun p => (JonesParshall.pr5 p).1 ∈ A ∧ (JonesParshall.pr5 p).2 ∈ A

@[expose] def SuppProp (A : Finset (Fin 5)) : Prop :=
  ∀ x y : Fin 5 → ZMod 2, (∃ p, minor x y p ≠ 0) → (∀ p ∉ pairsIn A, minor x y p = 0) →
    ∀ a ∉ A, x a = 0 ∧ y a = 0

theorem supp_01 : SuppProp {0, 1} := by unfold SuppProp; decide

theorem supp_012 : SuppProp {0, 1, 2} := by unfold SuppProp; decide

theorem supp_0123 : SuppProp {0, 1, 2, 3} := by unfold SuppProp; decide

theorem supp_1234 : SuppProp {1, 2, 3, 4} := by unfold SuppProp; decide

theorem wedgeMat_apply_eq_minor (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (k l : Fin 10) :
    JonesParshall.wedgeMat g k l =
      minor (fun a => g a (JonesParshall.pr5 l).1) (fun a => g a (JonesParshall.pr5 l).2) k := by
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, minor]
  ring

theorem coordFix_wedge_iff {A : Finset (Fin 5)} (hA : SuppProp A)
    (hA2 : ∀ c ∈ A, ∃ d ∈ A, d ≠ c) (g : SL5) :
    CoordFix (pairsIn A) (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔
      ∀ a ∉ A, ∀ c ∈ A, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a c = 0 := by
  constructor
  · intro h a ha c hc
    obtain ⟨d, hd, hdc⟩ := hA2 c hc
    obtain ⟨l, hl⟩ : ∃ l : Fin 10, JonesParshall.pr5 l = (c, d) ∨ JonesParshall.pr5 l = (d, c) := by
      rcases lt_or_gt_of_ne hdc with h1 | h1
      · obtain ⟨l, hl⟩ := exists_pr5 d c h1
        exact ⟨l, Or.inr hl⟩
      · obtain ⟨l, hl⟩ := exists_pr5 c d h1
        exact ⟨l, Or.inl hl⟩
    have hlA : l ∈ pairsIn A := by
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hl with hl | hl <;> rw [hl] <;> exact ⟨by assumption, by assumption⟩
    set x : Fin 5 → ZMod 2 := fun a => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a
      (JonesParshall.pr5 l).1
    set y : Fin 5 → ZMod 2 := fun a => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a
      (JonesParshall.pr5 l).2
    have hne : ∃ p, minor x y p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply wedgeMat_mulVec_single_ne g l
      funext k
      have hk : (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single l 1) k =
          JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hk, wedgeMat_apply_eq_minor]
      exact hcon k
    have hout : ∀ p ∉ pairsIn A, minor x y p = 0 := fun p hp => by
      rw [← wedgeMat_apply_eq_minor]
      exact h l hlA p hp
    obtain ⟨hx, hy⟩ := hA x y hne hout a ha
    rcases hl with hl | hl
    · simpa [x, hl] using hx
    · simpa [y, hl] using hy
  · intro h l hl k hk
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hl hk
    rw [wedgeMat_apply_eq_minor]
    simp only [minor]
    rcases hk with hk | hk
    · rw [h _ hk _ hl.1, h _ hk _ hl.2]
      ring
    · rw [h _ hk _ hl.1, h _ hk _ hl.2]
      ring

theorem pairsIn_01 : pairsIn {0, 1} = {0} := by decide

theorem pairsIn_012 : pairsIn {0, 1, 2} = {0, 1, 4} := by decide

theorem pairsIn_0123 : pairsIn {0, 1, 2, 3} = {0, 1, 2, 4, 5, 7} := by decide

theorem pairsIn_1234 : pairsIn {1, 2, 3, 4} = {4, 5, 6, 7, 8, 9} := by decide

theorem stabGam_iff (k : ℕ) (A : Finset (Fin 5)) (hA : ∀ j : Fin 5, j ∈ A ↔ j.val < k)
    (g : SL5) :
    (∀ a ∉ A, ∀ c ∈ A, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a c = 0) ↔ StabGam k g := by
  constructor
  · intro h i j hj hi
    exact h i (fun h' => by have := (hA i).1 h'; omega) j ((hA j).2 hj)
  · intro h a ha c hc
    exact h a c ((hA c).1 hc) (by
      by_contra hlt
      exact ha ((hA a).2 (by omega)))

theorem coordFix_V1_iff (g : SL5) :
    CoordFix {0} (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔
      StabGam 2 g := by
  rw [← pairsIn_01, coordFix_wedge_iff supp_01 (by decide) g]
  exact stabGam_iff 2 _ (by decide) g

theorem coordFix_V3_iff (g : SL5) :
    CoordFix {0, 1, 4} (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔
      StabGam 3 g := by
  rw [← pairsIn_012, coordFix_wedge_iff supp_012 (by decide) g]
  exact stabGam_iff 3 _ (by decide) g

theorem coordFix_V6_iff (g : SL5) :
    CoordFix {0, 1, 2, 4, 5, 7} (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔
      StabGam 4 g := by
  rw [← pairsIn_0123, coordFix_wedge_iff supp_0123 (by decide) g]
  exact stabGam_iff 4 _ (by decide) g

theorem coordFix_V4_iff (g : SL5) :
    CoordFix {0, 1, 2, 3} (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔
      StabGam 1 g := by
  have hc : ({0, 1, 2, 3} : Finset (Fin 10))ᶜ = pairsIn {1, 2, 3, 4} := by
    rw [pairsIn_1234]
    decide
  rw [coordFix_transpose, ← wedgeMat_transpose, hc,
    show (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = ((g.transpose : SL5) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) from (SpecialLinearGroup.coe_transpose g).symm,
    coordFix_wedge_iff supp_1234 (by decide) g.transpose]
  simp only [SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
  constructor
  · intro h i j hj hi
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    exact h 0 (by decide) i (by
      have : i ≠ 0 := fun h => by rw [h] at hi; exact absurd hi (by decide)
      revert this
      fin_cases i <;> decide)
  · intro h a ha c hc
    have ha0 : a = 0 := by
      revert ha
      fin_cases a <;> decide
    subst ha0
    exact h c 0 (by decide) (by
      revert hc
      fin_cases c <;> decide)

theorem coordFix_V7_of {g : SL5} (hg : StabGam 2 g) :
    CoordFix {0, 1, 2, 3, 4, 5, 6}
      (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
  intro l hl k hk
  rw [wedgeMat_apply_eq_minor]
  simp only [minor]
  have hl' : (JonesParshall.pr5 l).1.val < 2 := by
    revert l
    decide
  have hk' : 2 ≤ (JonesParshall.pr5 k).1.val ∧ 2 ≤ (JonesParshall.pr5 k).2.val := by
    revert k
    decide
  rw [hg _ _ hl' hk'.1, hg _ _ hl' hk'.2]
  ring

end S125W

end CFSG.Quasithin.H13
