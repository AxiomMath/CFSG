module

public import CFSG.Timmesfeld.Exceptional.SigmaTwoLines
public import CFSG.Timmesfeld.Exceptional.TOFiveA

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem orderOf_eq_five_of_mem_nbhd_four (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D)
    (hP1 : ExcP1 D) {p c : G} (hp : p ∈ D) (hc : c ∈ D) (hp4 : p ∈ nbhd D c 4)
    (hp3 : p ∉ nbhd D c 3) : orderOf (p * c) = 5 := by
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hTO := (totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).2 hp3
  obtain ⟨-, y, hy3, hpy⟩ := (mem_nbhd_succ_iff hc).1 hp4
  have hy := nbhd_subset hc 3 hy3
  have hy2 : y ∉ nbhd D c 2 := fun h => hp3 (mem_nbhd_succ_of_commute hp h hpy)
  obtain ⟨hpc, hoddpc⟩ := hTO.opposite_self hp
  obtain ⟨e, he, hep, -⟩ := exists_reflection hD hconj hp hc hoddpc
  obtain ⟨x, hx, hyx, -, hxc⟩ := exists_special_of_mem_nbhd_three hD hNL hNP hc hy3 hy2
  obtain ⟨⟨hvD, hpv, -⟩, hv3, hv2, hvy, hvpy⟩ :=
    FarLine.reflect hclass hD hNL hNP hPl hP1 hc hp hp3 he hep hy hpy hx hyx hxc rfl rfl
  have hyp : y ≠ p := fun h => hp3 (h ▸ hy3)
  have hvp : e * (x * c) ^ 2 * e ≠ p := fun h => hp3 (h ▸ hv3)
  have hpyD : p * y ∈ D := hNP p hp y hy hpy (Ne.symm hyp)
  have hsq : (y * (e * (x * c) ^ 2 * e)) ^ 2 = p := by
    rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl hp hy hvD hpy hpv hyp hvp with
      h | h | ⟨-, h⟩
    · exact absurd h hvy
    · exact absurd h hvpy
    · exact h
  have hopp := hTO _ hpyD ((Commute.refl p).mul_right hpy)
  exact orderOf_eq_five_of_two_lines_of_p1 hD hconj hNL hNP hPl hP1 hp hc hy hvD hpy hpv hsq
    (orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc hy3 hy2)
    (orderOf_eq_three_of_mem_nbhd_three hD hNL hNP hP1 hc hv3 hv2) hpc hoddpc hopp.1 hopp.2

@[expose] def ExcDiam4 (D : Set G) : Prop :=
  ∀ p ∈ D, ∀ c ∈ D, TotallyOpposite D p c → p ∈ nbhd D c 4

theorem excTO5_of_diam4 (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hNL : NoLevi D) (hNP : NoPolar D) (hPl : ExcNoPlane D) (hP1 : ExcP1 D)
    (h4 : ExcDiam4 D) : ExcTO5 D := fun p hp c hc hTO =>
  orderOf_eq_five_of_mem_nbhd_four hclass hD hNL hNP hPl hP1 hp hc (h4 p hp c hc hTO)
    ((totallyOpposite_iff_not_mem_nbhd_three hD hNL hc hp).1 hTO)

end CFSG.Timmesfeld.Moufang
