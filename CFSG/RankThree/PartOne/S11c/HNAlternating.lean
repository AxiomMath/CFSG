module

public import CFSG.RankThree.PartOne.S11c.HNProps
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)
open CFSG.RankThree.Classical (unitary_three_five_model)

theorem card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = Nat.factorial n / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem fiveFixedExcludesAlternating_holds : FiveFixedExcludesAlternating := by
  intro H _ _ hH X hX β K hK n hn ⟨f⟩
  obtain ⟨-, -, hmodel⟩ := hK
  let π : X →* alternatingGroup (Fin n) := f.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hπ : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ center X := by
    intro x hx
    have h1 : f (QuotientGroup.mk' (center X) x) = 1 := MonoidHom.mem_ker.mp hx
    have h2 : QuotientGroup.mk' (center X) x = 1 := by
      apply f.injective
      rw [h1, map_one]
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hn12 : n ≤ 12 :=
    (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
      (K := X) π hπ hker).2.2.1 hH
  have hK126 : Nat.card K = 126000 :=
    (unitary_three_five_model K hmodel).1
  have hdvd : 126000 ∣ Nat.factorial n / 2 := by
    have h1 := Subgroup.card_subgroup_dvd_card K
    rw [hK126, Nat.card_congr f.toEquiv, card_alternatingGroup_fin n (by omega)] at h1
    exact h1
  interval_cases n <;> norm_num [Nat.factorial] at hdvd

end CFSG.RankThree.PartOne.HNRed
