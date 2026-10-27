module

public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.Mathlib.GroupTheory.QuotCenterCardDvd
public import CFSG.Timmesfeld.Orders.PpdE8A8
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE8_A8_field
    {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) (hrank : labJ.rank = 8) (hdvd : n ∣ labJ.n) :
    labJ.n = n := by
  have hn1 : 1 ≤ n := hn.1
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨k, hk⟩ := hdvd
  have hk' : m = n * k := hk
  have hm1 : 1 ≤ m := hΛJ.1
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hnk_pos : 0 < n * k := by
      have hm0 : 0 < m := by omega
      rw [hk'] at hm0
      exact hm0
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, mul_zero] at hnk_pos
        omega
      · exact hkpos
    have hk_eq : k = 1 := by omega
    rw [hk_eq, mul_one] at hk'
    exact hk'
  · exfalso
    have hdiv := CFSG.GroupTheory.card_quotCenter_dvd_of_le hJX
    have hcardE : Nat.card (↥X ⧸ Subgroup.center ↥X) = ordE8 (2 ^ n) := by
      obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hX
      have hmodel := untwistedChevalleyModel_largeEven .E8 hK
      have hord :=
        CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E8 hmodel
      have hord' : Nat.card (LargeEvenCenterQuot
            (LargeEvenChevH (LargeEvenCartanE 8) K false)) = ordE8 (2 ^ n) := hord
      rw [Nat.card_congr e.toEquiv, hord']
    rw [hcardE] at hdiv
    rcases htag with htagA | htagTwA
    · have ht : t = .A := htagA
      subst ht
      have hr8 : r = 8 := hrank
      subst hr8
      have hmodel := statedClassicalModel_of_hasLabel_typeA hΛJ hJ
      have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 8 (2 ^ m) := by
        simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).1 rfl
      rw [hcardJ, hk'] at hdiv
      exact CFSG.Timmesfeld.Orders.ordA_eight_not_dvd_ordE8 hn1 hk2 hdiv
    · have ht : t = .twA := htagTwA
      subst ht
      have hr8 : r = 8 := hrank
      subst hr8
      have hmodel := statedClassicalModel_of_hasLabel_typeTwA hΛJ hJ
      have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 8 (2 ^ m) := by
        simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.1 rfl
      rw [hcardJ, hk'] at hdiv
      exact CFSG.Timmesfeld.Orders.ordTwistedA_eight_not_dvd_ordE8 hn1 hk2 hdiv

end CFSG.StandardType

end
