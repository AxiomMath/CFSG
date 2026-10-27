module

public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.Quasithin.EmptyFaithful.S151ZE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI
  CFSG.Quasithin.Vol2.Ch10.SecA

variable {G : Type} [Group G]

theorem not_a38Order_6048 : ¬ A38Order 6048 :=
  not_a38Order_of (a := 5) (b := 189) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (ordA_one_ne_of_lt (b := 6048) (B := 24) (by norm_num) (by
      intro p hpB hp hp3
      interval_cases p <;> decide))

theorem card_isPSL_two {X : Type} [Group X] {n : ℕ} (h : IsPSL n 2 1 X) :
    Nat.card X = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) := by
  obtain ⟨e⟩ := FLc.nonempty_equiv_SLt_of_isPSL h
  rw [Nat.card_congr e.toEquiv]
  exact Nat.card_congr (specialLinearGroupEquivStatedSL n (ZMod 2)).toEquiv

@[expose] def A6NotA38Type : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    (∃ α : ↥L →* alternatingGroup (Fin 6), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) →
      ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def G2NotA38Type : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
    ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

theorem a6NotA38Type_holds :
    A6NotA38Type := by
  intro G _ L ⟨α, hα, hk⟩ hA
  have hc := card_quot_pCore_of_surjective α hα hk
  rw [card_alt 6 (by norm_num)] at hc
  have h360 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
    rw [hc]
    decide
  exact not_a38Order_360 (h360 ▸ a38Order_card hA)

theorem g2NotA38Type_holds :
    G2NotA38Type := by
  intro G _ L hL hA
  have h6048 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 :=
    CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hL
  exact not_a38Order_6048 (h6048 ▸ a38Order_card hA)

theorem l45NotA38Type_holds :
    L45NotA38Type := by
  intro G _ L hL hA
  have hc := a38Order_card hA
  rcases hL with h4 | h5
  · rw [card_isPSL_two h4, card_statedSL_four_zmod1527d] at hc
    exact not_a38Order_20160 hc
  · rw [card_isPSL_two h5, card_statedSL_five_zmod1527d] at hc
    exact not_a38Order_9999360 hc

end CFSG.Quasithin
