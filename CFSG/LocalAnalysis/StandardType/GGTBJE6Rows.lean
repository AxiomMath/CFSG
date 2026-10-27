module

public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Mathlib.GroupTheory.QuotCenterCardDvd
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Orders.PpdE6D4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggE6_D4_field {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .D) (hrank : labJ.rank = 4) (hdvd : n ∣ labJ.n) : labJ.n = n := by
  have hn1 : 1 ≤ n := hn.1
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨k, hk⟩ := hdvd
  have hk' : m = n * k := hk
  have hm1 : 1 ≤ m := hΛJ.1
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, mul_zero] at hk'
        omega
      · exact hkpos
    have hk_eq : k = 1 := by omega
    rw [hk_eq, mul_one] at hk'
    exact hk'
  · exfalso
    have hdiv := CFSG.GroupTheory.card_quotCenter_dvd_of_le hJX
    have hcardE : Nat.card (↥X ⧸ Subgroup.center ↥X) = ordE6 (2 ^ n) := by
      obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hX
      have hmodel := untwistedChevalleyModel_largeEven .E6 hK
      have hord := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6 hmodel
      have hord' : Nat.card (LargeEvenCenterQuot
            (LargeEvenChevH (LargeEvenCartanE 6) K false)) = ordE6 (2 ^ n) := hord
      rw [Nat.card_congr e.toEquiv, hord']
    rw [hcardE] at hdiv
    have ht : t = .D := htag
    subst ht
    have hr4 : r = 4 := hrank
    subst hr4
    have hmodel := statedClassicalModel_of_hasLabel_typeD (by norm_num : 4 ≤ 4) hJ
    have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordD 4 (2 ^ m) := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
    rw [hcardJ, hk'] at hdiv
    exact CFSG.Timmesfeld.Orders.ordD_four_not_dvd_ordE6 hn1 hk2 hdiv

theorem ggTwE6_D4_field {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .D) (hrank : labJ.rank = 4) (hdvd : n ∣ labJ.n) : labJ.n = n := by
  have hn1 : 1 ≤ n := hn.1
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨k, hk⟩ := hdvd
  have hk' : m = n * k := hk
  have hm1 : 1 ≤ m := hΛJ.1
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, mul_zero] at hk'
        omega
      · exact hkpos
    have hk_eq : k = 1 := by omega
    rw [hk_eq, mul_one] at hk'
    exact hk'
  · exfalso
    have hdiv := CFSG.GroupTheory.card_quotCenter_dvd_of_le hJX
    have hcardE : Nat.card (↥X ⧸ Subgroup.center ↥X) = ordTwistedE6 (2 ^ n) := by
      have hX' := hX
      dsimp only [GGHasLabel, LargeEvenRawDatum] at hX'
      unfold LargeEvenRecipeTwisted at hX'
      obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hX'
      have hmodel : TwistedChevalleyModel
          (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) .E6
          (2 ^ n) := twistedChevalleyModel_largeEven .E6 hK
      have hord := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_E6_two hn1 hmodel
      rw [Nat.card_congr e.toEquiv, hord]
    rw [hcardE] at hdiv
    have ht : t = .D := htag
    subst ht
    have hr4 : r = 4 := hrank
    subst hr4
    have hmodel := statedClassicalModel_of_hasLabel_typeD (by norm_num : 4 ≤ 4) hJ
    have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordD 4 (2 ^ m) := by
      simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
    rw [hcardJ, hk'] at hdiv
    exact CFSG.Timmesfeld.Orders.ordD_four_not_dvd_ordTwistedE6 hn1 hk2 hdiv

theorem ggTwE6_triD4_field {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X)
    {n : ℕ} (hn : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .triD4) (hdvd : n ∣ labJ.n) : labJ.n = n := by
  have hn1 : 1 ≤ n := hn.1
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨k, hk⟩ := hdvd
  have hk' : m = n * k := hk
  have hm1 : 1 ≤ m := hΛJ.1
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, mul_zero] at hk'
        omega
      · exact hkpos
    have hk_eq : k = 1 := by omega
    rw [hk_eq, mul_one] at hk'
    exact hk'
  · exfalso
    have hdiv := CFSG.GroupTheory.card_quotCenter_dvd_of_le hJX
    have hcardE : Nat.card (↥X ⧸ Subgroup.center ↥X) = ordTwistedE6 (2 ^ n) := by
      have hX' := hX
      dsimp only [GGHasLabel, LargeEvenRawDatum] at hX'
      unfold LargeEvenRecipeTwisted at hX'
      obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hX'
      have hmodel : TwistedChevalleyModel
          (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) .E6
          (2 ^ n) := twistedChevalleyModel_largeEven .E6 hK
      have hord := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_E6_two hn1 hmodel
      rw [Nat.card_congr e.toEquiv, hord]
    rw [hcardE] at hdiv
    have ht : t = .triD4 := htag
    subst ht
    have hcardJ : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTrialityD4 (2 ^ m) := by
      have hJ' := hJ
      dsimp only [GGHasLabel, LargeEvenRawDatum] at hJ'
      unfold LargeEvenRecipeTwisted at hJ'
      obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hJ'
      have hmodel : TwistedChevalleyModel
          (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 m)) .D4
          (2 ^ m) := twistedChevalleyModel_largeEven .D4 hK
      have hord := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hm1 hmodel
      rw [Nat.card_congr e.toEquiv, hord]
    rw [hcardJ, hk'] at hdiv
    exact CFSG.Timmesfeld.Orders.ordTrialityD4_not_dvd_ordTwistedE6 hn1 hk2 hdiv

theorem ggTBJE6RowL_holds : GGTBJE6RowL := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  have hcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨ht, hr4, hp3, h3⟩ := hc
  have hfield : m = n := ggE6_D4_field hJL hΛ hhas hΛJ hhasJ ht hr4 hdvd
  obtain rfl : t = .D := ht
  obtain rfl : r = 4 := hr4
  subst hfield
  exact ⟨⟨.D, 4, m⟩, ⟨.E6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
    Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hp3, h3, rfl⟩)))⟩

theorem ggTBJE6RowK_holds : GGTBJE6RowK := by
  intro G _ _ p B Bs x L D J y K hH hJK hp hK hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨ht, hr4, hp3, h3⟩ := hc
  have hfield : m = n := ggE6_D4_field hJK hΛ hhas hΛJ hhasJ ht hr4 hdvd
  obtain rfl : t = .D := ht
  obtain rfl : r = 4 := hr4
  subst hfield
  exact ⟨⟨.D, 4, m⟩, ⟨.E6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
    Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hp3, h3, rfl⟩)))⟩

theorem ggTBJTwE6RowL_holds : GGTBJTwE6RowL := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  have hcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rcases hc with ⟨ht, hr4, hp3, h3⟩ | ⟨ht, hp3, h3⟩ | ⟨ht, hr2, hp3, h3m⟩
  · obtain ⟨t, r, m⟩ := labJ
    have hfield : m = n := ggTwE6_D4_field hJL hΛ hhas hΛJ hhasJ ht hr4 hdvd
    obtain rfl : t = .D := ht
    obtain rfl : r = 4 := hr4
    subst hfield
    exact ⟨⟨.D, 4, m⟩, ⟨.twE6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, hp3, h3, rfl⟩)))⟩
  · obtain ⟨t, r, m⟩ := labJ
    have hfield : m = n := ggTwE6_triD4_field hJL hΛ hhas hΛJ hhasJ ht hdvd
    subst hfield
    exact ⟨⟨t, r, m⟩, ⟨.twE6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hp3, h3, rfl⟩)))⟩
  · exact ⟨labJ, ⟨.twE6, 0, n⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hr2, hp3, rfl, h3m.symm⟩))))⟩

theorem ggTBJTwE6RowK_holds : GGTBJTwE6RowK := by
  intro G _ _ p B Bs x L D J y K hH hJK hp hK hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hc
  rcases hc with ⟨ht, hr4, hp3, h3⟩ | ⟨ht, hp3, h3⟩ | ⟨ht, hr2, hp3, h3m⟩
  · obtain ⟨t, r, m⟩ := labJ
    have hfield : m = n := ggTwE6_D4_field hJK hΛ hhas hΛJ hhasJ ht hr4 hdvd
    obtain rfl : t = .D := ht
    obtain rfl : r = 4 := hr4
    subst hfield
    exact ⟨⟨.D, 4, m⟩, ⟨.twE6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, hp3, h3, rfl⟩)))⟩
  · obtain ⟨t, r, m⟩ := labJ
    have hfield : m = n := ggTwE6_triD4_field hJK hΛ hhas hΛJ hhasJ ht hdvd
    subst hfield
    exact ⟨⟨t, r, m⟩, ⟨.twE6, 0, m⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hp3, h3, rfl⟩)))⟩
  · exact ⟨labJ, ⟨.twE6, 0, n⟩, hΛJ, hΛ, hhasJ, hhas,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hr2, hp3, rfl, h3m.symm⟩))))⟩

end CFSG.StandardType

end
