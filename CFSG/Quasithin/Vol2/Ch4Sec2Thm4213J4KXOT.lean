module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.Milestones.ASVolI.I3
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open

theorem le_pCore_of_normal_isPGroup {G : Type} [Group G] (p : ℕ) {N : Subgroup G} (hN : N.Normal)
    (hP : IsPGroup p N) : N ≤ CFSG.pCore p G := by
  rw [CFSG.pCore_eq_iSup]
  exact le_iSup₂_of_le N hN (le_iSup_of_le hP le_rfl)

theorem oddTwoCore_eq_center {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Nat.card (Subgroup.center K) = 6) (E0 : Subgroup (K ⧸ Subgroup.center K))
    (hE0 : IsElemAbelian 3 E0) (hE0c : Nat.card E0 = 9) :
    CFSG.ASVolI.ChIJK.oddTwoCore K = Subgroup.center K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.oddCore K with hOdef
  have hOodd : Odd (Nat.card O) := CFSG.ABGTheoremB.odd_card_oddCore K
  have hKeven : 2 ∣ Nat.card K := by
    have h6 : Nat.card (Subgroup.center K) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
    rw [hZ] at h6
    exact (by norm_num : 2 ∣ 6).trans h6
  have hOne : O ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top] at hOodd
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hKeven)
  have hOZ : O ≤ Subgroup.center K := by
    rcases normal_le_center_or_top hK O with h | h
    · exact h
    · exact absurd h hOne
  have h3 : 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ]; norm_num
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hcZ : (c : K) ∈ Subgroup.center K := c.2
  have hcN : (Subgroup.zpowers (c : K)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hgc : g * (c : K) * g⁻¹ = c := by
      have := Subgroup.mem_center_iff.mp hcZ g
      rw [this]
      group
    rw [← conj_zpow, hgc]
    exact Subgroup.zpow_mem_zpowers _ k
  have hord3 : orderOf (c : K) = 3 := (Subgroup.orderOf_coe c).trans hc
  have hcO : Subgroup.zpowers (c : K) ≤ O := by
    apply CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore
    · exact hcN
    · rw [Nat.card_zpowers, hord3]
      decide
  have hOcard : Nat.card O = 3 := by
    have h1 : 3 ≤ Nat.card O := by
      have := Subgroup.card_le_of_le hcO
      rwa [Nat.card_zpowers, hord3] at this
    have hd : Nat.card O ∣ 6 := by
      rw [← hZ]
      exact Subgroup.card_dvd_of_le hOZ
    have hmod := Nat.odd_iff.mp hOodd
    have hle : Nat.card O ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    generalize Nat.card O = m at h1 hd hmod hle ⊢
    interval_cases m <;> first | rfl | omega | norm_num at hd
  set Qm := K ⧸ O with hQmdef
  have hQm : CFSG.IsQuasisimple Qm := isQuasisimple_quot_of_le_center hK O hOZ
  have hZm := center_quot_eq hK.1.commutator_eq_top O hOZ
  have hZm2 : Nat.card (Subgroup.center Qm) = 2 := by
    set φ : ↥(Subgroup.center K) →* Qm := (QuotientGroup.mk' O).comp (Subgroup.center K).subtype
      with hφdef
    have hker : φ.ker = O.subgroupOf (Subgroup.center K) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφdef, MonoidHom.comp_apply,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hrange : φ.range = Subgroup.center Qm := by
      rw [hZm, hφdef, MonoidHom.range_comp, Subgroup.range_subtype]
    have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hkerc : Nat.card φ.ker = 3 := by
      rw [hker]
      have e := Subgroup.subgroupOfEquivOfLe hOZ
      rw [Nat.card_congr e.toEquiv, hOcard]
    have hq : Nat.card (↥(Subgroup.center K) ⧸ φ.ker) = Nat.card (Subgroup.center Qm) := by
      rw [← hrange]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hcZ6 : Nat.card ↥(Subgroup.center K) = 6 := hZ
    rw [hcZ6, hkerc, hq] at hdec
    omega
  set eQ : (Qm ⧸ Subgroup.center Qm) ≃* (K ⧸ Subgroup.center K) :=
    (QuotientGroup.quotientMulEquivOfEq hZm).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Subgroup.center K) hOZ) with heQdef
  have hpc : CFSG.pCore 2 Qm = Subgroup.center Qm := by
    apply le_antisymm
    · have hpn : CFSG.pCore 2 Qm ≤ Subgroup.center Qm ∨ CFSG.pCore 2 Qm = ⊤ :=
        normal_le_center_or_top hQm (CFSG.pCore 2 Qm)
      rcases hpn with h | htop
      · exact h
      · exfalso
        have hP2 : IsPGroup 2 (⊤ : Subgroup Qm) := by
          rw [← htop]
          exact CFSG.pCore_isPGroup
        have hP2q : IsPGroup 2 (⊤ : Subgroup (Qm ⧸ Subgroup.center Qm)) := by
          have := hP2.map (QuotientGroup.mk' (Subgroup.center Qm))
          rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2q
        have hn' : Nat.card (Qm ⧸ Subgroup.center Qm) = 2 ^ n := by
          rw [← Subgroup.card_top]
          exact hn
        have hc9 : Nat.card (E0.map eQ.symm.toMonoidHom) = 9 := by
          rw [Subgroup.card_map_of_injective eQ.symm.injective, hE0c]
        have hE9 : 9 ∣ 2 ^ n := by
          rw [← hn', ← hc9]
          exact Subgroup.card_subgroup_dvd_card _
        have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : (3 : ℕ) ∣ 9) hE9
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        norm_num at this
    · exact le_pCore_of_normal_isPGroup 2 inferInstance
        (IsPGroup.of_card (n := 1) (by rw [hZm2]; norm_num))
  unfold CFSG.ASVolI.ChIJK.oddTwoCore
  rw [hpc, hZm, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOZ]

end CFSG.Quasithin.H13.Ch4.J4KX
