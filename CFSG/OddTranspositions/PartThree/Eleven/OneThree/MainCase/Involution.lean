module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72

theorem pCore_le_twoOddCore (X : Type) [Group X] [Finite X] :
    CFSG.pCore 2 X ≤ EightOne.twoOddCore X := by
  intro z hz
  show z ∈ (CFSG.oddCore (X ⧸ CFSG.pCore 2 X)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 X))
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
  exact one_mem _

theorem mem_pCore_of_mem_twoOddCore_of_mul_self_eq_one {X : Type} [Group X] [Finite X] {k : X}
    (hk : k ∈ EightOne.twoOddCore X) (hk2 : k * k = 1) : k ∈ CFSG.pCore 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 X) k ∈
      CFSG.oddCore (X ⧸ CFSG.pCore 2 X) := by
    simpa [EightOne.twoOddCore] using hk
  have hsq : QuotientGroup.mk' (CFSG.pCore 2 X) k *
      QuotientGroup.mk' (CFSG.pCore 2 X) k = 1 := by
    rw [← map_mul, hk2, map_one]
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) k) ∣
      Nat.card (CFSG.oddCore (X ⧸ CFSG.pCore 2 X)) :=
    Subgroup.orderOf_dvd_natCard _ hk'
  have hodd := CFSG.ABGLocalTools.odd_card_oddCore (H := X ⧸ CFSG.pCore 2 X)
  have hone : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) k) = 1 := by
    have hdvd2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) k) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact h1
    · rw [h2] at hdvd
      exact absurd hdvd hodd.not_two_dvd_nat
  exact (QuotientGroup.eq_one_iff k).mp (orderOf_eq_one_iff.mp hone)

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_mul_sq_mem_pCore (hC : HypothesisC D) {c d : Halpha D hC.alpha}
    (hc : (c : G) ∈ D) (hd : (d : G) ∈ D)
    (hcd : (c * d) ^ 2 ∈ CFSG.pCore 2 (Halpha D hC.alpha)) : Commute (c : G) (d : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : (c : G) * (c : G) = 1 := hC.setup.oddT.mul_self_eq_one hc
  have hd2 : (d : G) * (d : G) = 1 := hC.setup.oddT.mul_self_eq_one hd
  let z : CFSG.pCore 2 (Halpha D hC.alpha) := ⟨(c * d) ^ 2, hcd⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha)).exists_orderOf_dvd_pow z
  have hzdiv : orderOf ((c * d) ^ 2) ∣ 2 ^ k := by
    rw [Subgroup.orderOf_coe z]
    exact hk
  have hydiv : orderOf (c * d) ∣ 2 * orderOf ((c * d) ^ 2) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  have hypow : orderOf (c * d) ∣ 2 ^ (k + 1) := by
    rw [pow_succ']
    exact hydiv.trans (Nat.mul_dvd_mul_left 2 hzdiv)
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hypow
  have hcases : orderOf (c * d) ∣ 2 ∨ Odd (orderOf (c * d)) := by
    rw [← Subgroup.orderOf_coe (c * d), Subgroup.coe_mul]
    exact hC.setup.oddT.2 (c : G) hc (d : G) hd
  rcases hcases with h2 | hodd
  · have hsqH : (c * d) * (c * d) = 1 := by
      simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h2
    have hsqG : ((c : G) * (d : G)) ^ 2 = 1 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using congrArg Subtype.val hsqH
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hc2 hd2).mpr hsqG
  · rw [hn] at hodd
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.pow_of_ne_zero hn0)
    have hcd1 : c * d = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hn, hn0, pow_zero]
    have hd2H : d * d = 1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hd2
    have hceq : c = d := by
      calc c = d⁻¹ := eq_inv_of_mul_eq_one_left hcd1
        _ = d := inv_eq_of_mul_eq_one_right hd2H
    simpa [hceq]

theorem mul_mem_pCore_of_mul_mem_twoOddCore (hC : HypothesisC D) {c v : Halpha D hC.alpha}
    (hc : (c : G) ∈ D) (hv : (v : G) ∈ D) (hcv : Commute (c : G) (v : G))
    (hK : c * v ∈ EightOne.twoOddCore (Halpha D hC.alpha)) :
    c * v ∈ CFSG.pCore 2 (Halpha D hC.alpha) := by
  have hc2 : (c : G) * (c : G) = 1 := hC.setup.oddT.mul_self_eq_one hc
  have hv2 : (v : G) * (v : G) = 1 := hC.setup.oddT.mul_self_eq_one hv
  have hsqG : (((c * v : Halpha D hC.alpha) : G) * ((c * v : Halpha D hC.alpha) : G)) = 1 := by
    rw [Subgroup.coe_mul]
    calc ((c : G) * (v : G)) * ((c : G) * (v : G))
        = ((c : G) * (v : G)) ^ 2 := by rw [pow_two]
      _ = (c : G) ^ 2 * (v : G) ^ 2 := hcv.mul_pow 2
      _ = 1 := by rw [pow_two, pow_two, hc2, hv2, mul_one]
  have hsq : (c * v) * (c * v) = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hsqG
  exact mem_pCore_of_mem_twoOddCore_of_mul_self_eq_one hK hsq

private theorem two_dvd_orderOf_mul_conj (hC : HypothesisC D) {c v : Halpha D hC.alpha}
    (hc : (c : G) ∈ D) (hv : (v : G) ∈ D) (hcv : Commute (c : G) (v : G))
    (hQ : c * v ∉ CFSG.pCore 2 (Halpha D hC.alpha)) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha)) :
    2 ∣ orderOf (c * (k * v * k⁻¹)) := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  let K := EightOne.twoOddCore H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  let b : H := k * v * k⁻¹
  have hKnot : c * v ∉ K := by
    intro hcvK
    exact hQ (mul_mem_pCore_of_mul_mem_twoOddCore hC hc hv hcv hcvK)
  have hπk : π k = 1 := (QuotientGroup.eq_one_iff (N := K) k).mpr hk
  have hπb : π b = π v := by
    simp [b, hπk]
  have hπcb : π (c * b) = π (c * v) := by
    rw [map_mul, hπb, ← map_mul]
  have hπcv_ne : π (c * v) ≠ 1 := by
    intro h1
    exact hKnot ((QuotientGroup.eq_one_iff (N := K) (c * v)).mp h1)
  have hcv2 : (c * v) * (c * v) = 1 := by
    have hc2 : (c : G) * (c : G) = 1 := hC.setup.oddT.mul_self_eq_one hc
    have hv2 : (v : G) * (v : G) = 1 := hC.setup.oddT.mul_self_eq_one hv
    have hsqG : (((c * v : H) : G) * ((c * v : H) : G)) = 1 := by
      rw [Subgroup.coe_mul]
      calc ((c : G) * (v : G)) * ((c : G) * (v : G))
          = ((c : G) * (v : G)) ^ 2 := by rw [pow_two]
        _ = (c : G) ^ 2 * (v : G) ^ 2 := hcv.mul_pow 2
        _ = 1 := by rw [pow_two, pow_two, hc2, hv2, mul_one]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hsqG
  have hπcb_sq : (π (c * b)) * (π (c * b)) = 1 := by
    rw [hπcb, ← map_mul, hcv2, map_one]
  have hπcb_ne : π (c * b) ≠ 1 := by
    rw [hπcb]
    exact hπcv_ne
  have hordπ : orderOf (π (c * b)) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hπcb_sq) hπcb_ne
  have hdvd : 2 ∣ orderOf (c * b) := by
    have h := orderOf_map_dvd π (c * b)
    rwa [hordπ] at h
  simpa [b] using hdvd

theorem commute_conj_of_mul_not_mem_pCore (hC : HypothesisC D) {c v : Halpha D hC.alpha}
    (hc : (c : G) ∈ D) (hv : (v : G) ∈ D) (hcv : Commute (c : G) (v : G))
    (hQ : c * v ∉ CFSG.pCore 2 (Halpha D hC.alpha)) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha)) :
    Commute (c : G) ((k : G) * v * (k : G)⁻¹) := by
  let H := Halpha D hC.alpha
  let b : H := k * v * k⁻¹
  have hdvd : 2 ∣ orderOf (c * b) := by
    simpa [b] using two_dvd_orderOf_mul_conj hC hc hv hcv hQ hk
  have hbD : (b : G) ∈ D := by
    simpa [b, Subgroup.coe_mul] using hC.setup.normal (k : G) (v : G) hv
  have hcases : orderOf (c * b) ∣ 2 ∨ Odd (orderOf (c * b)) := by
    rw [← Subgroup.orderOf_coe (c * b), Subgroup.coe_mul]
    exact hC.setup.oddT.2 (c : G) hc (b : G) hbD
  have hb2 : (b : G) * (b : G) = 1 := hC.setup.oddT.mul_self_eq_one hbD
  have hc2 : (c : G) * (c : G) = 1 := hC.setup.oddT.mul_self_eq_one hc
  rcases hcases with h2 | hodd
  · have hsqH : (c * b) * (c * b) = 1 := by
      simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h2
    have hsqG : ((c : G) * (b : G)) ^ 2 = 1 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using congrArg Subtype.val hsqH
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hc2 hb2).mpr hsqG
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd))

end CFSG.OddTranspositions.PartThree.ElevenThree
