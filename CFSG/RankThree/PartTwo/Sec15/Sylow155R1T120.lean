module

public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_n155_of_isPGroup {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K Q : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hQ : IsPGroup 2 ↥Q) (hQ1 : Q ≠ ⊥)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (Q : Set G) ≤ n155 A K :=
  Sec15.le_n155_of_isPLocal h153 hK (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hQ hQ1)
    (sup_le hKQ hAQ)

theorem eq_bot_of_not_le_n155 {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K Q E : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hQ : IsPGroup 2 ↥Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hE : ¬ E ≤ n155 A K) : Q = ⊥ := by
  by_contra hQ1
  exact hE (hEQ.trans (normalizer_le_n155_of_isPGroup h153 hK hQ hQ1 hAQ hKQ))

theorem centralizer_le_n155 {A : Subgroup G} (h153 : Item153Main A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) {z : G} (hz : orderOf z = 2)
    (hzA : A ≤ Subgroup.centralizer ({z} : Set G)) (hzK : K ≤ Subgroup.centralizer ({z} : Set G)) :
    Subgroup.centralizer ({z} : Set G) ≤ n155 A K := by
  have hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute z g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    exact (hc.zpow_left k).eq
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hQ1 : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    rintro rfl
    simp at hz
  exact hCN.trans (normalizer_le_n155_of_isPGroup h153 hK hQ hQ1 (hzA.trans hCN) (hzK.trans hCN))

theorem le_n155_of_le_centralizer {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K E : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) {z : G} (hz : orderOf z = 2)
    (hzA : A ≤ Subgroup.centralizer ({z} : Set G)) (hzK : K ≤ Subgroup.centralizer ({z} : Set G))
    (hE : E ≤ Subgroup.centralizer ({z} : Set G)) : E ≤ n155 A K :=
  hE.trans (centralizer_le_n155 h153 hK hz hzA hzK)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
