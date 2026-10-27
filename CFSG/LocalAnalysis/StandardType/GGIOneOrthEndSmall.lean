module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace IOneOrthEnd

theorem card_of_isU42 {X : Type*} [Group X] (h : LargeEvenIsU42 X) : Nat.card X = 25920 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) (p := 2) (f := 1)
    (n := 4) Nat.prime_two le_rfl (by rw [hF]; norm_num) (by norm_num)
  simp only [pow_one] at h1
  exact h1.trans (by decide)

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem not_largeEvenSmall_of_seven_dvd {G : Type*} [Group G] {K : Subgroup G}
    (h7 : 7 ∣ Nat.card K) : ¬ LargeEvenSmall K := by
  rintro (hU | hA)
  · rw [card_of_isU42 hU] at h7
    omega
  · obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six] at h7
    omega

theorem not_largeEvenSmall_of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (h7 : 7 ∣ Nat.card (K.map f)) : ¬ LargeEvenSmall K :=
  not_largeEvenSmall_of_seven_dvd (h7.trans (Subgroup.card_map_dvd K f))

end IOneOrthEnd

end CFSG.StandardType
