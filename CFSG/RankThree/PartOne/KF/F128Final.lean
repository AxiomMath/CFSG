module

public import CFSG.RankThree.PartOne.KF.F128Lie
public import CFSG.RankThree.PartOne.KF.F128Cyclic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FieldFix
open CFSG.Blueprint (LieModel EvenLieType)

variable {G : Type} [Group G]

theorem kf128_of_rank_one
    [Finite G] (hT : ∀ t, TagFixedFacts t) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {J E : Subgroup G} {a d : G} (hq : CFSG.IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hJ : CFSG.pRank p ↥J ≤ 1)
    (hEel : IsElementaryAbelian p E) (hEN : E ≤ Subgroup.normalizer (J : Set G)) (haE : a ∈ E)
    (hdE : d ∈ E) (hdJ : d ∈ J) (hd1 : d ≠ 1) (hfa : InducesFieldAut p a J) :
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
  have : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
  have hdp : d ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) d hdE
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hpJ : p ∣ Nat.card J := by
    have := orderOf_dvd_natCard (⟨d, hdJ⟩ : J)
    rwa [Subgroup.orderOf_mk, hdord] at this
  exact kf128_of_moves hp (by omega) hJ hEel hEN hdE hdJ hd1
    (fun S hS => fieldAut_moves_sylow hT hp h5 hq hZ hJ hpJ hap hfa hS)

end CFSG.RankThree.PartOne
