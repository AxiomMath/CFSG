module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.PGroupFixedPrimeElement

open MulAction

private theorem exists_fixed_order_prime
    {p : ℕ} [Fact p.Prime] (K H : Type*) [Group K] [Group H] [Finite H]
    [MulDistribMulAction K H] (hK : IsPGroup p K) (hH : p ∣ Nat.card H) :
    ∃ b : H, orderOf b = p ∧ ∀ k : K, k • b = b := by
  let C := FixedPoints.subgroup K H
  have hm := hK.card_modEq_card_fixedPoints H
  have hc : p ∣ Nat.card C := by
    change Nat.card H % p = Nat.card C % p at hm
    exact Nat.dvd_of_mod_eq_zero (hm.symm.trans (Nat.mod_eq_zero_of_dvd hH))
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' p hc
  exact ⟨b.val,(Subgroup.orderOf_coe b).trans hb,
    (FixedPoints.mem_subgroup K H b.val).mp b.property⟩

private theorem exists_commuting_order_prime
    {p : ℕ} [Fact p.Prime] (G : Type*) [Group G]
    (H K : Subgroup G) [Finite H] (hH : p ∣ Nat.card H) (hK : IsPGroup p K)
    (hnorm : K ≤ Subgroup.normalizer (H : Set G)) :
    ∃ b : G, b ∈ H ∧ orderOf b = p ∧ ∀ k : G, k ∈ K → Commute b k := by
  let f : K →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  let _ : MulDistribMulAction K H := MulDistribMulAction.compHom H f
  obtain ⟨b,hb,hfixed⟩ := exists_fixed_order_prime K H hK hH
  refine ⟨b.val,b.property,(Subgroup.orderOf_coe b).trans hb,?_⟩
  intro k hk
  have he := congrArg Subtype.val (hfixed ⟨k,hk⟩)
  change (H.normalizerMonoidHom ⟨k,hnorm hk⟩ b).val = b.val at he
  rw [H.normalizerMonoidHom_apply_apply_coe ⟨k,hnorm hk⟩ b] at he
  have hc := congrArg (fun z : G => z * k) he
  simp only [mul_assoc,inv_mul_cancel,mul_one] at hc
  exact hc.symm

theorem exists_commuting_involution
    (G : Type*) [Group G] (H K : Subgroup G) [Finite H]
    (hH : Even (Nat.card H)) (hK : IsPGroup 2 K)
    (hnorm : K ≤ Subgroup.normalizer (H : Set G)) :
    ∃ b : G, b ∈ H ∧ orderOf b = 2 ∧ ∀ k : G, k ∈ K → Commute b k :=
  exists_commuting_order_prime G H K (even_iff_two_dvd.mp hH) hK hnorm

end FiveTransitive.PGroupFixedPrimeElement

end CFSG
