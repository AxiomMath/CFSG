module

public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.JonesParshallG2Field

public section

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Open
open scoped commutatorElement

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

theorem card_g2_two {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) : Nat.card ↥H = 12096 := by
  have : CharP K 2 := Vol2.KGNat.charP_two_of_card (n := 1) (by norm_num) (by rw [hK]; norm_num)
  rw [Nat.card_congr e.toEquiv, quasithinG2_eq_cayleyGroup, Vol2.KGNat.card_cayleyGroup, hK]
  norm_num

theorem card_commutator_g2_two
    {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) : Nat.card ↥⁅H, H⁆ = 6048 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := nonempty_commutator_equiv e
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  let F : ↥⁅H, H⁆ ≃* U33G := (((f1.trans f2).trans f3).trans u33EquivSubG2.symm)
  rw [Nat.card_congr F.toEquiv]
  exact card_u33Pres

theorem commutator_ne_g2_two
    {Ω : Type*} [Group Ω] {H : Subgroup Ω} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥H ≃* ↥(quasithinG2 K)) : ⁅H, H⁆ ≠ H := by
  intro h
  have h1 := card_commutator_g2_two hK e
  rw [h, card_g2_two hK e] at h1
  omega

end CFSG.Quasithin.F918X
