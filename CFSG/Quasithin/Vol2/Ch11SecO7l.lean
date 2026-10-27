module

public import CFSG.Quasithin.Vol2.Ch11SecO7k
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem card_of_isAlt6 {L : Type} [Group L] (h : IsAlt 6 L) : Nat.card L = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_of_isAlt7 {L : Type} [Group L] (h : IsAlt 7 L) : Nat.card L = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_of_isHatAlt6 {L : Type} [Group L] (h : IsHat L (alternatingGroup (Fin 6))) :
    Nat.card L = 1080 := by
  rw [SecA.C10KH.card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_of_isHatAlt7 {L : Type} [Group L] (h : IsHat L (alternatingGroup (Fin 7))) :
    Nat.card L = 7560 := by
  rw [SecA.C10KH.card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_of_isPSU35 {L : Type} [Group L] (h : IsPSU 3 5 1 L) : Nat.card L = 126000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h

theorem card_of_isSU35 {L : Type} [Group L] (h : IsSU3 5 L) : Nat.card L = 378000 := by
  rw [SecA.C11P9B.card_of_isSU3 h]
  norm_num

theorem card_of_isSL35 {L : Type} [Group L] (h : IsSL3 5 L) : Nat.card L = 372000 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
    3 K).symm).toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num),
    hK]
  decide

theorem not_isExt_of_odd_dvd {B : Type} [Group B] [Finite B] {a d : ℕ}
    (hB : Nat.card B = 2 ^ a * 15) (hd : Odd d) (h15 : ¬ d ∣ 15)
    {PV PY : ∀ (V : Type) [Group V], Prop} (hY : ∀ (Q : Type) [Group Q], PY Q → d ∣ Nat.card Q) :
    ¬ IsExt B PV PY := by
  rintro ⟨V, hVn, -, hQ⟩
  exact h15 (dvd_fifteen hd (hB ▸ (hY _ hQ).trans (Subgroup.card_quotient_dvd_card V)))

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
