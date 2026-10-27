module

public import CFSG.Timmesfeld.Exceptional.TOFiveA

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ThreeNear (D : Set G) (z a : G) : Prop :=
  ∃ x : Fin 3 → G, (∀ i, x i ∈ collinearSet D a) ∧ (∀ i, x i ∈ nbhd D z 3) ∧
    ∀ i j, i ≠ j → x j ≠ x i ∧ x j ≠ a * x i

theorem threeNear_of_two_special (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {z a y s₁ s₂ : G} (hz : z ∈ D) (ha : a ∈ D) (ha3 : a ∉ nbhd D z 3)
    (hy : y ∈ collinearSet D a) (hy3 : y ∈ nbhd D z 3) (hs₁ : s₁ ∈ D) (hys₁ : Commute y s₁)
    (h₁ : orderOf (s₁ * z) = 4) (hs₂ : s₂ ∈ D) (hys₂ : Commute y s₂)
    (h₂ : orderOf (s₂ * z) = 4) (hne : s₁ ≠ s₂) : ThreeNear D z a := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  obtain ⟨hyD, hay, hayD⟩ := hy
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hz ha).2 ha3
  obtain ⟨-, hodd⟩ := hTO.opposite_self ha
  obtain ⟨e, he, hea, -⟩ := exists_reflection hD hconj ha hz hodd
  have hy2 : y ∉ nbhd D z 2 := fun h => ha3 (mem_nbhd_succ_of_commute ha h hay)
  obtain ⟨hv₁, hv₁3, -, hv₁y, hv₁ay⟩ := FarLine.reflect hclass hD hNL hNP hPl hP1 hz ha ha3 he hea
    hyD hay hs₁ hys₁ h₁ rfl rfl
  obtain ⟨hv₂, hv₂3, -, hv₂y, hv₂ay⟩ := FarLine.reflect hclass hD hNL hNP hPl hP1 hz ha ha3 he hea
    hyD hay hs₂ hys₂ h₂ rfl rfl
  set v₁ := e * (s₁ * z) ^ 2 * e with hv₁_def
  set v₂ := e * (s₂ * z) ^ 2 * e with hv₂_def
  have h12 : v₁ ≠ v₂ := fun h =>
    hne (FarLine.eq_of_reflect_eq hD hconj hNL hNP hPl hz hyD hy2 hs₁ hys₁ h₁ hs₂ hys₂ h₂ h)
  have h1a2 : v₁ ≠ a * v₂ :=
    FarLine.ne_mul_reflect hclass hD hNL hNP hPl hz he hea hyD hy2 hs₁ hys₁ h₁ hs₂ hys₂ h₂
  have h2a1 : v₂ ≠ a * v₁ :=
    FarLine.ne_mul_reflect hclass hD hNL hNP hPl hz he hea hyD hy2 hs₂ hys₂ h₂ hs₁ hys₁ h₁
  have ha2 := hD.mul_self_eq_one ha
  have hflip : ∀ u w : G, u ≠ a * w → w ≠ a * u := fun u w h e => h (by
    rw [e, ← mul_assoc, ha2, one_mul])
  refine ⟨![y, v₁, v₂], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hyD, hay, hayD⟩
    · exact hv₁
    · exact hv₂
  · intro i
    fin_cases i
    · exact hy3
    · exact hv₁3
    · exact hv₂3
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
    · exact ⟨hv₁y, hv₁ay⟩
    · exact ⟨hv₂y, hv₂ay⟩
    · exact ⟨Ne.symm hv₁y, hflip _ _ hv₁ay⟩
    · exact ⟨Ne.symm h12, h2a1⟩
    · exact ⟨Ne.symm hv₂y, hflip _ _ hv₂ay⟩
    · exact ⟨h12, h1a2⟩

theorem eq_of_not_threeNear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {z a y s₁ s₂ : G} (hz : z ∈ D) (ha : a ∈ D) (ha3 : a ∉ nbhd D z 3)
    (hy : y ∈ collinearSet D a) (hy3 : y ∈ nbhd D z 3) (hs₁ : s₁ ∈ D) (hys₁ : Commute y s₁)
    (h₁ : orderOf (s₁ * z) = 4) (hs₂ : s₂ ∈ D) (hys₂ : Commute y s₂)
    (h₂ : orderOf (s₂ * z) = 4) (hnot : ¬ ThreeNear D z a) : s₂ = s₁ := by
  by_contra hne
  exact hnot (threeNear_of_two_special hclass hD hNL hNP hPl hP1 hz ha ha3 hy hy3 hs₁ hys₁ h₁ hs₂
    hys₂ h₂ (Ne.symm hne))

theorem special_of_mem_nbhd_three (hD : IsRootInvolutionSet D) (hNL : NoLevi D)
    (hNP : NoPolar D) (hP1 : ExcP1 D) {z y q : G} (hz : z ∈ D) (hy : y ∈ D)
    (hy3 : y ∈ nbhd D z 3) (hy2 : y ∉ nbhd D z 2) (hq : q ∈ collinearSet D y)
    (hq3 : q ∈ nbhd D z 3) : orderOf (q * z) = 4 ∨ orderOf (y * q * z) = 4 := by
  obtain ⟨hqD, hyq, hyqD⟩ := hq
  by_cases hq2 : q ∈ nbhd D z 2
  · rcases (mem_nbhd_two_iff hD hNL hz).1 hq2 with ⟨-, hqz | h4⟩
    · exact absurd (mem_nbhd_succ_of_commute hy ((mem_nbhd_one_iff hz).2 ⟨hqD, hqz⟩) hyq) hy2
    · exact Or.inl h4
  · have h3y := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hz hy3 hy2
    have h3q := orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hz hq3 hq2
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hyqD hz with hc | h4 | ⟨hodd, -⟩
    · exfalso
      refine hy2 (mem_nbhd_succ_of_commute hy ((mem_nbhd_one_iff hz).2 ⟨hyqD, hc⟩) ?_)
      exact (Commute.refl y).mul_right hyq
    · exact Or.inr h4
    · exact (false_of_orderOf_three_three_of_line (hD.mul_self_eq_one hy)
        (hD.mul_self_eq_one hqD) (hD.mul_self_eq_one hz) hyq h3y h3q hodd).elim

end CFSG.Timmesfeld.Moufang.Deep
