module

public import CFSG.RankThree.PartTwo.KFacts.KFOut3Shape
public import CFSG.RankThree.PartTwo.Sec4.Item49Closed

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem le_inner_of_oddOThreePrime {X : Type} [Group X]
    (h : Odd (Nat.card (Sec4.oThreePrime (Outer X)))) {β : MulAut X}
    (hβ : IsPGroup 3 (Subgroup.zpowers β)) {T : Subgroup (MulAut X)} (hT : IsPGroup 2 T)
    (hTβ : ⁅T, Subgroup.zpowers β⁆ = T) : T ≤ inner X := by
  set π : MulAut X →* Outer X := QuotientGroup.mk' (inner X) with hπ
  have hcomm : ⁅T, Subgroup.zpowers β⁆ ≤ (Sec4.oThreePrime (Outer X)).comap π := by
    rw [Subgroup.commutator_le]
    intro t _ b hb
    obtain ⟨n, hn⟩ := hβ ⟨b, hb⟩
    have hb3 : b ^ 3 ^ n = 1 := congrArg Subtype.val hn
    have hπb : π b ^ 3 ^ n = 1 := by rw [← map_pow, hb3, map_one]
    have hπc : (π t * π b * (π t)⁻¹) ^ 3 ^ n = 1 := by
      rw [conj_pow, hπb, mul_one, mul_inv_cancel]
    have hπbi : (π b)⁻¹ ^ 3 ^ n = 1 := by rw [inv_pow, hπb, inv_one]
    rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    exact mul_mem (Sec4.mem_oThreePrime_of_pow hπc) (Sec4.mem_oThreePrime_of_pow hπbi)
  intro t ht
  have htO : π t ∈ Sec4.oThreePrime (Outer X) := hcomm (hTβ.symm ▸ ht)
  obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
  have ht2 : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hord2 : orderOf (⟨π t, htO⟩ : Sec4.oThreePrime (Outer X)) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, ht2, map_one]))
  have hordc : orderOf (⟨π t, htO⟩ : Sec4.oThreePrime (Outer X)) ∣
      Nat.card (Sec4.oThreePrime (Outer X)) :=
    orderOf_dvd_natCard _
  have hord1 : orderOf (⟨π t, htO⟩ : Sec4.oThreePrime (Outer X)) = 1 := by
    have hcop : Nat.Coprime (2 ^ n) (Nat.card (Sec4.oThreePrime (Outer X))) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr h)
    exact Nat.eq_one_of_dvd_coprimes hcop hord2 hordc
  have h1 : π t = 1 := by
    have := orderOf_eq_one_iff.mp hord1
    exact congrArg Subtype.val this
  exact (QuotientGroup.eq_one_iff t).mp h1

theorem kfOut3_of_inputs49 (h : Sec4.Inputs49) : KFOut3 :=
  kfOut3_of_le_inner fun X _ _ hq h46 _ hβ _ hT hTβ =>
    le_inner_of_oddOThreePrime (h.oddOThreePrime X h46 hq) hβ hT hTβ


theorem kfOut3_holds : KFOut3 :=
  kfOut3_of_inputs49 Sec4.inputs49

end CFSG.RankThree.PartTwo.KFacts
