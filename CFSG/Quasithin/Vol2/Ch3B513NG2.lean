module

public import CFSG.Quasithin.Vol2.Ch3B513NG2C
public import CFSG.Quasithin.Vol2.Ch3B513NC1
public import CFSG.Quasithin.Background.SmithB51G2DOff

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem c1g2_holds (hIdent : AsB42Ident) (h42 : AsB42) (hA21 : AsA21SQTKSection)
    (hG2D : C1G2Der) : C1G2 := by
  intro W _ _ hW G hsolv hne hB53 h1 hGL hU n hG2
  have hperf : ⁅G, G⁆ = G := by
    have := Subgroup.isPerfect_iff.mp h1.1.1
    rwa [← hGL] at this
  rcases Nat.lt_or_ge n 2 with hn | hn
  ·
    have hn1 : n = 1 := by
      obtain ⟨K, _, _, hK, -⟩ := hG2
      interval_cases n
      · have : 1 < Nat.card K := Finite.one_lt_card
        simp at hK
        omega
      · rfl
    subst hn1
    have e := B5.g2NaturalDerived_of_g2Natural hG2
    rw [hperf] at e
    exact hG2D W hW G hne hB53 h1 hGL hU e
  ·
    obtain ⟨K, _, _, hK, π, hr⟩ := id hG2
    have : Fintype K := Fintype.ofFinite K
    have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    have : CharP K 2 := charP_of_card_eq_prime_pow hF
    have hinv : ∀ x ∈ G, ∀ v ∈ commV G, x v ∈ commV G := fun x hx v hv =>
      hU.2.1 ⟨x, hx⟩ v hv
    have hC := card_fixV_le_of_g2 hW G (commV G) hinv hU.2.2.1 hn hK ⟨π, hr⟩
    have hB51 : B51Hyp G G := by
      have := b51Hyp_of_case1 hA21 hB53 h1
      rwa [← hGL] at this
    have hUc := G64.RealizesVia.card_eq hr
    rw [B5.G2D.card_zornQMod, hK] at hUc
    have hCU : fixV G ⊓ commV G ≤ commV G := inf_le_right
    have hUs : Nat.card (commV G) = Nat.card (Sec (commV G) (fixV G ⊓ commV G)) *
        Nat.card ↥(fixV G ⊓ commV G) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((fixV G ⊓ commV G).subgroupOf (commV G))]
      congr 1
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
    have hcardS : Nat.card (Sec (commV G) (fixV G ⊓ commV G)) = (2 ^ n) ^ 6 := by
      rw [hUs] at hUc
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hUc
    have hL : B5.G2D.G2Orders G n := by
      right
      refine ⟨hn, ?_⟩
      have hinj := FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hr
      have hc : Nat.card ↥(quasithinG2 K) = Nat.card G :=
        Nat.card_congr (Equiv.ofBijective π ⟨hinj, hr.1⟩)
      rw [← hc, card_quasithinG2_1527d hK, hK]
    obtain ⟨D, hD⟩ := exists_isFFStarMin hne hB53.2.1
    obtain ⟨-, hDc, hfix, hfixc⟩ :=
      B5.G2D.offender_facts hIdent h42 hW hB51 hU (by omega) hcardS hL hD.1
    refine hasGood_of_offender_le hW hD (commV_mono hD.1.1) ?_
    rw [inf_comm, ← hfix, hfixc, hDc]
    calc Nat.card ↥(fixV G ⊓ commV G) * 2 ^ (3 * n) ≤ 2 ^ n * 2 ^ (3 * n) :=
          Nat.mul_le_mul_right _ hC
      _ ≤ (2 ^ (3 * n)) ^ 2 := by
          rw [← pow_add, ← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.B513N
