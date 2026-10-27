module

import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering88

theorem theta_inf_le_theta {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H) :
    inSubgroup (aschbacherSolvableCore 3) H ⊓ K ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨hs, h3⟩ := Sec6.theta_solvable_and_not_dvd H
  set N := inSubgroup (aschbacherSolvableCore 3) H ⊓ K with hN
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Sec6.le_normalizer_theta H (hKH hx), Subgroup.le_normalizer hx⟩
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : N ≤ inSubgroup (aschbacherSolvableCore 3) H))
      (Subgroup.inclusion_injective _)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact Sec6.le_theta_of_normal inf_le_right hKN hNsol hN3

theorem commutator_inf_le {G : Type} [Group G] (M K : Subgroup G) : ⁅M ⊓ K, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgK : g ∈ K := (Subgroup.mem_inf.mp hg).2
  simp only [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hgK hh) (K.inv_mem hgK)) (K.inv_mem hh)

end Hering88

end CFSG.RankThree.PartTwo.Sec8
