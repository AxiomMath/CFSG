module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_false_of_normalizer_zpowers_le (hSE : StronglyEmbeddedFive)
    (hS : Standing G) (S : Setup G) {p : ℕ} (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig)
    (hp5 : 5 ≤ p) (hsp : IsStronglyPEmbedded p S.M) {R : Subgroup G} {x z : G} {ℓ : ℕ}
    (hR : R ≠ ⊥) (hRM : R ≤ S.M) (hN : ¬ normalizer (R : Set G) ≤ S.M)
    (hrank : 2 ≤ CFSG.Open.pRank p (S.M ⊓ normalizer (R : Set G)))
    (hxN : x ∈ normalizer (R : Set G) ⊓ S.M) (hzN : z ∈ normalizer (R : Set G) ⊓ S.M)
    (hx : orderOf x = p) (hxz : x * z = z * x) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p)
    (hz : orderOf z = ℓ) (hNz : normalizer ((zpowers z : Subgroup G) : Set G) ≤ S.M) : False := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hH : Sec7Core4.Config k (normalizer (R : Set G)) :=
    k.config_normalizer hR hRM hrank hN
  have hxp : IsPGroup k.p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]; rfl)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  obtain ⟨j, hjM, hjz⟩ := k.exists_not_mem_commute_of_prime (k.step75 hp5 hSE) k.step72L
    (k.step76C_of_kIDExcluded hp5 (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hSE)
    hH hxN hzN hxp hx1 (by rw [hz]; exact hℓ) (by rw [hz]; exact hℓ2) (by rw [hz]; exact hℓp) hxz
  have hjC : j ∈ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    exact ((Commute.zpow_right (show Commute j z from hjz) i).eq).symm
  exact hjM (hNz (Subgroup.centralizer_le_normalizer _ hjC))

theorem uc22s2121e3_false_of_routeZ_r847E3 (hSE : StronglyEmbeddedFive) (hS : Standing G)
    (S : Setup G) (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p)
    (hsp : IsStronglyPEmbedded p S.M) {R : Subgroup G} {x z : G} {Y : Subgroup G} {ℓ : ℕ}
    (hR : R ≠ ⊥) (hRM : R ≤ S.M) (hN : ¬ normalizer (R : Set G) ≤ S.M)
    (hrank : 2 ≤ CFSG.Open.pRank p (S.M ⊓ normalizer (R : Set G)))
    (hxN : x ∈ normalizer (R : Set G) ⊓ S.M) (hzN : z ∈ normalizer (R : Set G) ⊓ S.M)
    (hx : orderOf x = p) (hxz : x * z = z * x) (hY : Y ∈ calC S.M)
    (hYN : (Y.subgroupOf S.M).Normal) (hzY : z ∈ Y) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p)
    (hz : orderOf z = ℓ) (hcase : F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ ℓ ∣ 2 ^ n - 1) :
    False := by
  refine uc22s2121e3_false_of_normalizer_zpowers_le hSE hS S hp hp5 hsp hR hRM hN hrank hxN hzN
    hx hxz hℓ hℓ2 hℓp hz ?_
  have hzc : Nat.card (zpowers z) = ℓ := by rw [Nat.card_zpowers, hz]
  rcases hcase with hthin | ⟨n, hYn, hℓn⟩
  · rcases h847T Y hY hYN hthin (zpowers z) (zpowers_le.mpr hzY) ℓ hℓ hℓ2 hzc p hp with
      h | ⟨h3, -⟩
    · exact h
    · omega
  · rcases h847S Y hY hYN n hYn (zpowers z) (zpowers_le.mpr hzY) ℓ hℓ hℓ2 hℓn hzc p hp with
      h | ⟨h3, -⟩
    · exact h
    · omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
