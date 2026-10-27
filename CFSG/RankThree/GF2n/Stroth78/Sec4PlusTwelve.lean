module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTwelveSylow
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6RootClass

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
import CFSG.Adapters.LieModelOrders

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem not_lieModel_psp_three_of_card_ZQ_eq_four
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSp 3 2 1 := by
  intro hX
  have hD := rootClass_Xsub S h h217 h34
  refine false_of_sylow_three_bound S h h217 h34 hw4 hZ ?_ ?_ ?_
  · rw [hX.card_psp_three_two]
    norm_num
  · exact CFSG.ComponentClassification.Foote5.card_outer_eq_one_of_psp_three_two
      (hX.statedClassicalModel (by decide))
  · intro r hr P A hA2 hAc hrA hAr hAP
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hr1, hr2⟩ := hD.1.2.2.1 r hr
    have hro : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
    exact CFSG.EvenSmallLie.Sp6.card_le_eight_of_rootClass hX hD.1.2.1 hD.1.2.2.2.1 hD.2.1 hr
      hro P A hA2 hAc hAr hAP

end CFSG.RankThree.GF2n.Stroth78
