module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

theorem IsBenderGroup.exists_involution_commute_ne {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {u : K} (hu : orderOf u = 2) :
    ∃ t : K, orderOf t = 2 ∧ t ≠ u ∧ Commute u t := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    simp [h] at hu
  have hjp : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨Q, hQ⟩ := hjp.exists_le_sylow
  have huQ : u ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers u)
  set Z := Subgroup.center (Q : Subgroup K)
  have hcard : 4 ≤ Nat.card Z := IsBenderGroup.four_le_card_center hK Q
  have hnotsub : ¬ (Z : Set Q) ⊆ ({1, (⟨u, huQ⟩ : Q)} : Set Q) := by
    intro hsub
    have hle : Nat.card Z ≤ 2 := by
      calc Nat.card Z = (Z : Set Q).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, (⟨u, huQ⟩ : Q)} : Set Q).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 2 := Set.ncard_pair (by
            intro h
            exact hu1 (congrArg Subtype.val h).symm)
    omega
  rw [Set.not_subset] at hnotsub
  obtain ⟨tz, htz, htn⟩ := hnotsub
  have ht1 : tz ≠ 1 := fun h => htn (by simp [h])
  have htu : tz ≠ (⟨u, huQ⟩ : Q) := fun h => htn (by simp [h])
  let t : K := (tz : Q)
  have htQ : t ∈ Q := tz.2
  have htcomm : ∀ y ∈ Q, Commute t y := fun y hy =>
    (Subtype.ext_iff.1 (Subgroup.mem_center_iff.1 htz ⟨y, hy⟩)).symm
  have ht2 : t * t = 1 := IsBenderGroup.mul_self_eq_one_of_commute hK Q htQ htcomm
  have hto : orderOf t = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) fun h => ht1 (Subtype.ext h)
  refine ⟨t, hto, fun h => htu (Subtype.ext h), ?_⟩
  exact IsBenderGroup.commute_of_mul_self_eq_one hK Q huQ hu2 t htQ

end CFSG.Timmesfeld.Bridge.Asc72
