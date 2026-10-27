module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8Typed
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBTorLiftE8 :
    GGTBTorLiftE8 := by
  intro lab _ htag
  by_cases h3 : 3 ∣ 2 ^ lab.n + 1
  · have hE : 8 - ggTorEnn 3 lab = ggNbrExcPlusRank lab.tag := by
      rw [htag]
      simp [ggTorEnn, h3, ggNbrExcPlusRank]
    rw [hE]
    exact largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by norm_num)
      ⟨Or.inr (Or.inl htag), h3⟩
  · have h2 : ¬ 3 ∣ 2 ^ lab.n := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have h3' : 3 ∣ 2 ^ lab.n - 1 := by omega
    have hE : 8 - ggTorEnn 3 lab = 8 := by simp [ggTorEnn, h3]
    rw [hE]
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag h3'
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3'
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TableBExc.ggTorusLift_E8 Nat.prime_three (by norm_num) hpq⟩

end CFSG.StandardType

end
