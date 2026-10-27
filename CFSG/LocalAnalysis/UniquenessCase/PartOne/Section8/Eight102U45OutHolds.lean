module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.Adapters.LieModelUnitaryOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem kU45Out_holds : KU45Out := by
  intro X _ _ n h α hα h3
  rcases h with ⟨hU5, rfl⟩ | ⟨hU4, -⟩
  · obtain ⟨k, hk⟩ := h3
    have hout : Nat.card (Outer X) = 20 := by
      rw [CFSG.Blueprint.LieModel.card_outer_psu hU5 (by norm_num) (by norm_num)]
      norm_num
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer X)) := by
      rw [hout]
      exact Nat.Coprime.pow_left k (by norm_num)
    have h1 : (QuotientGroup.mk α : Outer X) ^ (3 ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    have h2 := pow_gcd_eq_one.2 ⟨h1, pow_card_eq_one' (G := Outer X)⟩
    rw [hcop.gcd_eq_one, pow_one] at h2
    exact (QuotientGroup.eq_one_iff (N := inner X) α).1 h2
  · have := PartTwo.Inputs1719.isCyclic_outer_of_lieModel_PSU4 hU4
    let _ : CommGroup (Outer X) := IsCyclic.commGroup
    have hker := Abelianization.commutator_subset_ker (QuotientGroup.mk' (inner X)) hα
    rw [QuotientGroup.ker_mk'] at hker
    exact hker

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
