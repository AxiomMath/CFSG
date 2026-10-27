module

public import CFSG.Quasithin.EmptyFaithful.S153YA3Main
public import CFSG.Quasithin.EmptyFaithful.S153YT3C
public import CFSG.Quasithin.EmptyFaithful.S153YBig

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input1469C61A3_proved : Input1469C61A3 := by
  intro G _ _ I S Iz K ρ _ hchar hmp hbp _ h3 hρN hρS hρ2 hb
  obtain ⟨-, hcomm, hgen, hperm₀, hperm₁, htrans⟩ := YG.blockProduct_two_data hbp h3
  have hM₀N : S ⊔ Subgroup.zpowers ρ ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hρN)
  have m := YG.gmate_of_zpowers hρN hρS hρ2 hb
  have hth : ⁅K 0, thompsonJ S⁆ = K 0 :=
    YG.thompson_a3_pair hmp.isSylow (hbp.2.2.1 0).1 (hbp.2.2.1 1).1 (h3 0) (h3 1) hcomm hperm₀ hperm₁
      hgen htrans hM₀N m.hC52
  exact YG.card_le_a3_pair_of_thompson hchar hmp hbp h3 hth hρN hρS hρ2 hb

theorem input1469C61Big_proved : Input1469C61Big :=
  input1469C61Big_of_a3 input1469C61A3_proved

end CFSG.Quasithin
