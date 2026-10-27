module

public import CFSG.Timmesfeld.Closure.LS

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

theorem commute_of_conj_mem_rootSet [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d f : G} (hd : d ∈ D) (hf : f ∈ D)
    (hfd : f * d * f⁻¹ ∈ rootSet D d) : Commute d f := by
  have hd2 := hD.mul_self_eq_one hd
  have hf2 := hD.mul_self_eq_one hf
  have hfinv : f⁻¹ = f := hD.inv_eq hf
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hf with hc | h4 | ⟨hodd, hnc⟩
  · exact hc
  · obtain ⟨hzD, -, hfz, hede⟩ := sq_mem_of_orderOf_eq_four hD hd hf h4
    rw [hfinv, hede] at hfd
    have hzW : (d * f) ^ 2 ∈ rootGroup D d := by
      have h := (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
        (rootSet_subset_rootGroup D d hfd)
      rwa [← mul_assoc, hd2, one_mul] at h
    have hzT := mem_rootSet_of_mem_rootGroup hclass hd hzD hzW
    exact (hzT.2 f hf).1 hfz.symm
  · exfalso
    have hcomm : Commute d (f * d * f⁻¹) := commute_of_mem_rootSet hd (mem_rootSet_self hd) hfd
    have hsq : d * (f * d * f⁻¹) = (d * f) ^ 2 := by rw [hfinv, pow_two]; group
    have h1 := (commute_iff_mul_sq_eq_one hd2 (by
      rw [show f * d * f⁻¹ * (f * d * f⁻¹) = f * (d * d) * f⁻¹ by group, hd2, mul_one,
        mul_inv_cancel])).1 hcomm
    rw [hsq, ← pow_mul] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    have h1' : orderOf (d * f) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_left.2 hodd).symm)
        (by simpa using hdvd)
    apply hnc
    have : d * f = 1 := orderOf_eq_one_iff.1 h1'
    have hfd' : f = d := by
      have := eq_inv_of_mul_eq_one_right this
      rwa [hD.inv_eq hd] at this
    rw [hfd']

theorem commute_of_mem_normalizer_rootGroup [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d f : G} (hd : d ∈ D) (hf : f ∈ D)
    (hfn : f ∈ Subgroup.normalizer (rootGroup D d : Set G)) : Commute d f := by
  refine commute_of_conj_mem_rootSet hclass hD hd hf ?_
  have hmem : f * d * f⁻¹ ∈ rootGroup D d :=
    (Subgroup.mem_normalizer_iff.1 hfn d).1 (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  exact mem_rootSet_of_mem_rootGroup hclass hd (conj_mem_of_isClass hclass f hd) hmem

end CFSG.Timmesfeld.Bridge
