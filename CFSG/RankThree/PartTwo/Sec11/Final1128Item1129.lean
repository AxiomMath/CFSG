module

import CFSG.RankThree.PartTwo.Sec11.Item1133Proof
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Item1129Proof

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_commutator {P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    y ∈ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) := by
  have key : ∀ w ∈ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, w * z * w⁻¹ ∈ ⁅P, P⁆ := by
    intro w hw z hz
    rw [Subgroup.commutator_def] at hz
    refine Item1133Proof.conj_mem_of_mem_closure ?_ hz
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have e : w * ⁅p, q⁆ * w⁻¹ = ⁅w * p * w⁻¹, w * q * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hw p).mp hp)
      ((Subgroup.mem_normalizer_iff.mp hw q).mp hq)
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key y hy z, fun hz => ?_⟩
  have h1 := key y⁻¹ (Subgroup.inv_mem _ hy) _ hz
  have e : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
  rwa [e] at h1

end General

end Item1129Proof

end CFSG.RankThree.PartTwo.Sec11
