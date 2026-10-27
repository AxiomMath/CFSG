module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishPair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Open

namespace OmegaMinusFourTrans

section Reach

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reach_symm {x y : V} (h : ∃ g ∈ elementaryGroup Q, g x = y) :
    ∃ g ∈ elementaryGroup Q, g y = x := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, inv_mem hg, LinearEquiv.inv_apply_apply' g x⟩

theorem reach_trans {x y z : V} (h₁ : ∃ g ∈ elementaryGroup Q, g x = y)
    (h₂ : ∃ g ∈ elementaryGroup Q, g y = z) : ∃ g ∈ elementaryGroup Q, g x = z := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨g', hg', rfl⟩ := h₂
  exact ⟨g' * g, mul_mem hg' hg, rfl⟩

theorem reach_step {u x y : V} (hu : Q u = 0) (hxy : Q x = Q y) {t : K}
    (hx : polar Q u x = t) (hy : polar Q u y = t) (ht : t ≠ 0) :
    ∃ g ∈ elementaryGroup Q, g x = y :=
  ⟨eichler Q u (t⁻¹ • (y - x)), eichler_mem_elementaryGroup Q _ _,
    eichler_apply_eq_of_polar_eq hu hxy hx hy ht⟩

end Reach

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

abbrev i₀ : Fin (2 - 1) := ⟨0, by norm_num⟩

@[expose] def vec (a d s t : K) : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K
  | .inl _ => a
  | .inr (.inl _) => d
  | .inr (.inr j) => if j = 0 then s else t

theorem quadMinus_vec (a d s t : K) :
    quadMinus 2 K b c (vec a d s t) = a * d + (s ^ 2 + b * s * t + c * t ^ 2) := by
  rw [quadMinus_apply]
  simp [vec]
  ring

theorem polar_e_vec (a d s t : K) :
    polar (quadMinus 2 K b c) (minusPair K b c i₀).e (vec a d s t) = d := by
  rw [minusPair_e, polar_single_inl_quadMinus]
  rfl

theorem polar_f_vec (a d s t : K) :
    polar (quadMinus 2 K b c) (minusPair K b c i₀).f (vec a d s t) = a := by
  rw [minusPair_f, polar_single_inr_quadMinus]
  rfl

theorem eq_vec (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    x = vec (x (.inl i₀)) (x (.inr (.inl i₀))) (x (.inr (.inr 0))) (x (.inr (.inr 1))) := by
  funext k
  rcases k with i | i | j
  · have hi : i = i₀ := Fin.ext (by have := i.isLt; simp only [i₀]; omega)
    rw [hi]; rfl
  · have hi : i = i₀ := Fin.ext (by have := i.isLt; simp only [i₀]; omega)
    rw [hi]; rfl
  · fin_cases j <;> rfl

theorem binary_eq_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {s t : K}
    (h : s ^ 2 + b * s * t + c * t ^ 2 = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hirr (s / t)
    field_simp
    linear_combination h

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
include hirr

theorem reach_smul_f {β : K} (hβ : β ≠ 0) :
    ∃ g ∈ elementaryGroup (quadMinus 2 K b c), g (vec 0 β 0 0) = vec 0 1 0 0 := by
  have hQe := (minusPair K b c i₀).Q_e
  have hQf := (minusPair K b c i₀).Q_f
  obtain ⟨⟨s, t⟩, hst⟩ := CFSG.GroupTheory.WeirSylow.exists_binForm_eq hirr β⁻¹
  rw [CFSG.GroupTheory.WeirSylow.binForm_apply] at hst
  have h0 : quadMinus 2 K b c (vec (0 : K) β 0 0) = 0 := by rw [quadMinus_vec]; ring
  have h1 : quadMinus 2 K b c (vec β⁻¹ β 1 0) = 0 := by
    rw [quadMinus_vec, inv_mul_cancel₀ hβ]
    simpa using CharTwo.add_self_eq_zero (1 : K)
  have h2 : quadMinus 2 K b c (vec β⁻¹ 1 s t) = 0 := by
    rw [quadMinus_vec, hst, mul_one]
    exact CharTwo.add_self_eq_zero _
  have h3 : quadMinus 2 K b c (vec (0 : K) 1 0 0) = 0 := by rw [quadMinus_vec]; ring
  refine reach_trans (reach_step hQe (h0.trans h1.symm) (polar_e_vec _ _ _ _)
    (polar_e_vec _ _ _ _) hβ) (reach_trans (reach_step hQf (h1.trans h2.symm)
      (polar_f_vec _ _ _ _) (polar_f_vec _ _ _ _) (inv_ne_zero hβ))
      (reach_step hQe (h2.trans h3.symm) (polar_e_vec _ _ _ _) (polar_e_vec _ _ _ _)
        one_ne_zero))

theorem reach_f {x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hx : x ≠ 0)
    (hx0 : quadMinus 2 K b c x = 0) :
    ∃ g ∈ elementaryGroup (quadMinus 2 K b c), g x = vec 0 1 0 0 := by
  have hQe := (minusPair K b c i₀).Q_e
  have hQf := (minusPair K b c i₀).Q_f
  have key : ∀ y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, quadMinus 2 K b c y = 0 →
      y (.inr (.inl i₀)) ≠ 0 →
      ∃ g ∈ elementaryGroup (quadMinus 2 K b c), g y = vec 0 1 0 0 := by
    intro y hy0 hβ
    have h0 : quadMinus 2 K b c (vec (0 : K) (y (.inr (.inl i₀))) 0 0) = 0 := by
      rw [quadMinus_vec]; ring
    have hpy : polar (quadMinus 2 K b c) (minusPair K b c i₀).e y = y (.inr (.inl i₀)) := by
      conv_lhs => rw [eq_vec y]
      exact polar_e_vec _ _ _ _
    exact reach_trans (reach_step hQe (hy0.trans h0.symm) hpy (polar_e_vec _ _ _ _) hβ)
      (reach_smul_f hirr hβ)
  by_cases hβ : x (.inr (.inl i₀)) = 0
  · set α := x (.inl i₀) with hα
    have hx' := eq_vec x
    rw [hβ] at hx'
    have hQx : x (.inr (.inr 0)) ^ 2 + b * x (.inr (.inr 0)) * x (.inr (.inr 1)) +
        c * x (.inr (.inr 1)) ^ 2 = 0 := by
      have := hx0
      rw [hx', quadMinus_vec, mul_zero, zero_add] at this
      exact this
    obtain ⟨hs, ht⟩ := binary_eq_zero hirr hQx
    rw [hs, ht] at hx'
    have hα0 : α ≠ 0 := by
      intro h0
      apply hx
      rw [hx', ← hα, h0]
      funext k
      rcases k with i | i | j
      · rfl
      · rfl
      · simp [vec]
    have hz : quadMinus 2 K b c (vec α α⁻¹ 1 0) = 0 := by
      rw [quadMinus_vec, mul_inv_cancel₀ hα0]
      simpa using CharTwo.add_self_eq_zero (1 : K)
    have hpx : polar (quadMinus 2 K b c) (minusPair K b c i₀).f x = α := by
      conv_lhs => rw [eq_vec x]
      exact polar_f_vec _ _ _ _
    refine reach_trans (reach_step hQf (hx0.trans hz.symm) hpx (polar_f_vec _ _ _ _) hα0)
      (key _ hz ?_)
    show α⁻¹ ≠ 0
    exact inv_ne_zero hα0
  · exact key x hx0 hβ

end OmegaMinusFourTrans

open OmegaMinusFourTrans in
theorem omegaMinusFourSingularTrans_holds : OmegaMinusFourSingularTransStatement := by
  intro K _ _ _ b c hirr x y hx hy hx0 hy0
  obtain ⟨g, hg, hgx⟩ := reach_trans (reach_f hirr hx hx0) (reach_symm (reach_f hirr hy hy0))
  refine ⟨((statedOmegaMinusEquiv le_rfl hirr).symm ⟨g, hg⟩ :
    StatedOmega (StatedQuadMinus 2 K b c)), Subtype.property _, ?_⟩
  rw [statedOmegaMinusEquiv_symm_app le_rfl hirr]
  exact hgx

end CFSG.RankThree.GF2n.Stroth80
