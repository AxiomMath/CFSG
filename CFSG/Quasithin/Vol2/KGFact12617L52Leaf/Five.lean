module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs

public section

namespace CFSG.Quasithin.H13.KG12617L52

theorem leafFive_holds : LeafFive := by
  intro H _ _ B hB
  obtain ⟨φ, hφ, -⟩ := hB
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hdvd : Nat.card ↥(alternatingGroup (Fin 6)) ∣ Nat.card ↥B :=
    Subgroup.card_dvd_of_surjective hφ
  rw [h360] at hdvd
  have h5 : 5 ∣ Nat.card ↥B := (by norm_num : (5 : ℕ) ∣ 360).trans hdvd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  exact ⟨(y : H), y.2, (Subgroup.orderOf_coe y).trans hy⟩

end CFSG.Quasithin.H13.KG12617L52
