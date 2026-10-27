module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CosetEvenBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CosetOddIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CosetEvenRepresentative
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The unconditional A7 outside-coset involution bound -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Every coset represented by an involution outside `M` contains at most
twenty-one involutions in the A7 branch. -/
public theorem secondCase_a7_coset_involutions_card_le_21
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M) :
    Nat.card {x : G // IsInvolution x ∧
      x ∈ (w.M : Set G) * ({y} : Set G)} ≤ 21 := by
  by_cases hDeven : Even (Nat.card
      (w.M ⊓ conjugateSubgroup w.M y : Subgroup G))
  · obtain ⟨z, hz, hzM, hzH, hcard⟩ :=
      secondCase_a7_exists_centralizing_coset_representative_of_even_intersection
        hmin c w d hA7 hmodel hy hyM hDeven
    rw [hcard]
    exact (secondCase_a7_coset_involutions_card_le_18_of_mem_H
      hmin c w d hA7 hmodel od hz hzM hzH).trans (by omega)
  · have hDodd : Odd (Nat.card
        (w.M ⊓ conjugateSubgroup w.M y : Subgroup G)) :=
      Nat.not_even_iff_odd.mp hDeven
    exact secondCase_a7_coset_involutions_card_le_21_of_odd_intersection
      hmin c w d hA7 hmodel od hy hyM hDodd

end CFSG.GorensteinWalter
