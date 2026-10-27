module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.GH74.Uniqueness.Bender

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem isPGroup_of_strongWC {T : Subgroup K} (hT : StrongWC T) : IsPGroup 2 T := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hT.1.2 x x.2)⟩

theorem eq_rootCenter_of_strongWC {n i e : ℕ} (h : BenderType K n i e) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) : ∃ Q : Sylow 2 K, T = rootCenter (Q : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := (isPGroup_of_strongWC hT).exists_le_sylow
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  refine ⟨Q, le_antisymm (fun x hx => ?_) (fun z hz => ?_)⟩
  · by_cases hx1 : x = 1
    · rw [hx1]
      exact (rootCenter _).one_mem
    · exact hc.center_of_involution x (le_borel _ (hTQ hx)) (orderOf_eq_prime (hT.1.2 x hx) hx1)
  · by_cases hz1 : z = 1
    · rw [hz1]
      exact T.one_mem
    obtain ⟨⟨t, ht⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have ht1 : t ≠ 1 := fun h' => ht1' (Subtype.ext h')
    have htt : t * t = 1 := by rw [← sq]; exact hT.1.2 t ht
    obtain ⟨c, hcz⟩ := isConj_iff.mp (h.lemma_3_4_a htt ht1 (hc.center_sq z hz) hz1)
    have hzt : (c⁻¹)⁻¹ * t * c⁻¹ ∈ Subgroup.centralizer ({t} : Set K) := by
      rw [inv_inv, hcz, Subgroup.mem_centralizer_singleton_iff]
      exact ((mem_rootCenter_iff.mp hz).2 t (hTQ ht)).symm
    have := hT.2 t ht ht1 t ht c⁻¹ hzt
    rwa [inv_inv, hcz] at this

theorem card_eq_of_strongWC {n i e : ℕ} (h : BenderType K n i e) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) : Nat.card T = 2 ^ n := by
  obtain ⟨Q, hQ⟩ := eq_rootCenter_of_strongWC h hT hT1
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  rw [hQ]
  exact hc.card_center

theorem card_eq_two_of_dihedral {m : ℕ} (hm : Odd m) (e : K ≃* DihedralGroup m)
    {T : Subgroup K} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) : Nat.card T = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT2
  have hdvd : Nat.card T ∣ 2 * m := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card T
  rw [hk] at hdvd ⊢
  rcases k with _ | _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq T (by simpa using hk)) hT1
  · norm_num
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 * m := (pow_dvd_pow 2 (show 2 ≤ k + 2 by omega)).trans hdvd
    obtain ⟨j, hj⟩ := hm
    norm_num at h4
    omega

end CFSG.RankThree.GF2n
