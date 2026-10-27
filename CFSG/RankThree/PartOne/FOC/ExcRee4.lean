module

public import CFSG.RankThree.PartOne.FOCD.ExcFinite
public import CFSG.RankThree.PartOne.FOC.SylowInner
public import CFSG.RankThree.PartOne.FOC.ExcRee4Split
public import CFSG.RankThree.PartOne.FOC.ExcRee4Sylow
public import CFSG.RankThree.PartOne.FOC.ExcRee4Outer
public import CFSG.RankThree.PartOne.KEXC.TwF4
public import CFSG.RankThree.PartOne.K133X.F4
public import CFSG.RankThree.PartOne.FOC.CompEquiv

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD

section Ree


theorem innerCompN_ree {T : Type} [Group T] [Finite T] [IsSimpleGroup T] {a f p : ℕ} (ha : 1 ≤ a)
    (hfa : f = 2 * a + 1) (hR : ReeTitsModel T .twistedF4 2 f) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : T ≃* ReeTag.F4.reeGamma K a) (hp : p.Prime) (hp5 : 5 ≤ p) : InnerCompN p T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hab, hA⟩ := sylowData_ree hK e hp hp5
  refine innerCompN_of_sylow hp hab hA ?_
  by_cases hpq : p ∣ 2 ^ (2 * a + 1) - 1
  · right
    intro b hb1 hbp E hE
    have hb1' : e b ≠ 1 := fun h => hb1 (e.injective (h.trans (map_one e).symm))
    have hbord : orderOf (e b) = p := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hbp hb1
    exact compDvdAt_of_mulEquiv e (compDvdAt_ree_split ha hK hp (by omega) hpq (e b) hbord) E hE
  · left
    refine KEXC.kf123ExcTwF4NoRankTwo_holds T f hR p hp hp5 ?_
    rw [hfa]
    exact hpq

theorem fieldInnerIdx_reeF4 (m : ℕ) : FieldInnerIdx (.reeF4 m) := by
  intro T _ _ p hp hp5 hs hnab hiso
  obtain ⟨-, hR⟩ := K133X.reeTitsModel_twistedF4_of_isoLie hiso
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := Sec66T.reeF4_model_data hR
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hfa]
  exact fieldInnerT_of_compN (center_eq_bot_of_nonab hs hnab)
    (innerCompN_ree ha hfa hR hK e hp hp5)
    (OuterComp.of_mulEquiv e hp (outerComp_ree ha hK hp hp5))

end Ree

end CFSG.RankThree.PartOne.FOC
