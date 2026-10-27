module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Odd subgroups of commuting two-by-odd products -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd-order subgroup contained in `W \sup U`, where `W` is a
`2`-group commuting elementwise with `U` and both factors are normal and
disjoint, lies in `U`. -/
public theorem odd_order_subgroup_le_of_le_sup_of_twoPGroup
    {G : Type u} [Group G] [Finite G]
    (W U K : Subgroup G)
    (hWnorm : IsNormalIn W (W ⊔ U))
    (hUnorm : IsNormalIn U (W ⊔ U))
    (hWU : ∀ w : G, w ∈ W → ∀ u : G, u ∈ U → w * u = u * w)
    (hK : K ≤ W ⊔ U)
    (hWp : IsPGroup 2 W)
    (hKodd : Odd (Nat.card K))
    (hdisj : Disjoint W U) :
    K ≤ U := by
  intro k hk
  let H : Subgroup G := W ⊔ U
  let W' : Subgroup H := W.subgroupOf H
  let U' : Subgroup H := U.subgroupOf H
  have hHleNW : H ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh w hw
    exact hWnorm.2 h hh w hw
  have hHleNU : H ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh u hu
    exact hUnorm.2 h hh u hu
  have hW'norm : W'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := W)
      hHleNW
  have hU'norm : U'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := U)
      hHleNU
  have htop : W' ⊔ U' = ⊤ := by
    dsimp [W', U', H]
    rw [← Subgroup.subgroupOf_sup (le_sup_left : W ≤ W ⊔ U)
      (le_sup_right : U ≤ W ⊔ U), Subgroup.subgroupOf_self]
  let : U'.Normal := hU'norm
  have hkSup : (⟨k, hK hk⟩ : H) ∈ W' ⊔ U' := by
    rw [htop]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := W') (t := U')
      (x := (⟨k, hK hk⟩ : H))).mp hkSup with
    ⟨w', hwW', u', huU', hwueq⟩
  have hwW : (w' : G) ∈ W := Subgroup.mem_subgroupOf.mp hwW'
  have huU : (u' : G) ∈ U := Subgroup.mem_subgroupOf.mp huU'
  have hkEq : (w' : G) * (u' : G) = k := congrArg Subtype.val hwueq
  have hordKodd : Odd (orderOf k) := by
    have hsub : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
    have hord : orderOf k = Nat.card (Subgroup.zpowers k) :=
      (Nat.card_zpowers k).symm
    have hdvd : orderOf k ∣ Nat.card K := by
      rw [hord]
      exact Subgroup.card_dvd_of_le hsub
    exact Odd.of_dvd_nat hKodd hdvd
  let n : ℕ := orderOf k
  have hpow : k ^ n = 1 := pow_orderOf_eq_one k
  have hcomm : Commute (w' : G) (u' : G) :=
    hWU (w' : G) hwW (u' : G) huU
  have hkpow : k ^ n = (w' : G) ^ n * (u' : G) ^ n := by
    rw [← hkEq]
    exact hcomm.mul_pow n
  have hwun : (w' : G) ^ n * (u' : G) ^ n = 1 := by
    rwa [hkpow] at hpow
  have hwn : (w' : G) ^ n = 1 := by
    have hwinW : (w' : G) ^ n ∈ W := W.pow_mem hwW n
    have huinU : (u' : G) ^ n ∈ U := U.pow_mem huU n
    have hwEqInv : (w' : G) ^ n = ((u' : G) ^ n)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hwun
    have hwinU : (w' : G) ^ n ∈ U := by
      rw [hwEqInv]
      exact U.inv_mem huinU
    exact Subgroup.disjoint_def.mp hdisj hwinW hwinU
  have hw1 : (w' : G) = 1 := by
    have hdvdn : orderOf (w' : G) ∣ n :=
      orderOf_dvd_iff_pow_eq_one.mpr hwn
    rcases hWp.exists_card_eq with ⟨m, hm⟩
    have hdvd2 : orderOf (w' : G) ∣ 2 ^ m := by
      have hsub : Subgroup.zpowers (w' : G) ≤ W :=
        Subgroup.zpowers_le.mpr hwW
      have hord : orderOf (w' : G) =
          Nat.card (Subgroup.zpowers (w' : G)) :=
        (Nat.card_zpowers (w' : G)).symm
      have hdvd : orderOf (w' : G) ∣ Nat.card W := by
        rw [hord]
        exact Subgroup.card_dvd_of_le hsub
      rwa [hm] at hdvd
    have hdvd1 : orderOf (w' : G) ∣ 1 := by
      have hgcd : Nat.gcd n (2 ^ m) = 1 :=
        ((Nat.coprime_two_left.mpr hordKodd).symm.pow_right m).gcd_eq_one
      rw [← hgcd]
      exact Nat.dvd_gcd hdvdn hdvd2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  simpa [← hkEq, hw1] using huU

end CFSG.GorensteinWalter
