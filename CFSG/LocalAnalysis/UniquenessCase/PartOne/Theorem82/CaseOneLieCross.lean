module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneAbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneMechanisms
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pow_two_mul_sub_one_eq (r f : ℕ) (hr : 0 < r) :
    r ^ (2 * f) - 1 = qMinusPi r f * qPlusPi r f := by
  have hq : 1 ≤ r ^ f := Nat.one_le_pow f r hr
  have hsq : r ^ (2 * f) = r ^ f * r ^ f := by
    rw [two_mul, pow_add]
  rw [hsq]
  unfold qMinusPi qPlusPi
  split_ifs with h
  · rw [Nat.sub_mul, one_mul, Nat.mul_add, Nat.mul_one]
    omega
  · rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_mul, Nat.one_mul]
    omega

namespace Case811Sylow

theorem false_of_ne_char_of_forall_pElement {c : Counterexample4 G} (h : Case811Sylow c) (hK7 : K7)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) (hpr : p ≠ r)
    (hpA : ∀ g ∈ c.S.M ⊓ Subgroup.normalizer (h.A : Set G), IsPGroup p (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (h.A : Set G)) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  have hM4 : 4 ≤ CFSG.Open.pRank p c.S.M := c.four_le_pRank_of_mem_sigma hp
  have hrprime : r.Prime := by
    rcases fam with _ | _ | _ | _ | _ | _ <;> exact hlie.2.2.1
  have hrpos : 0 < r := hrprime.pos
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hK := hK7 c.Lbar fam r f hlie p hp.1.1 hp5 hpr h.Abar h.isElemAbelian_Abar h.card_Abar
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at hK
  have hcentA : CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Counterexample4.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  have hCA_dvd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Counterexample4.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  have hcentX : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (X : Set G)) =
        CFSG.Open.pRank p (Subgroup.centralizer
          (((X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) :
            Set c.Lbar)) :=
    fun X hXA _ => Counterexample4.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
      (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)
  have hC : CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (h.A : Set G)) ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (h.A : Set G)) := by omega
    obtain ⟨R, hRle, hR, hRcard⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p) hp.1.1 (k := 2) h2
    exact h.false_of_le_centralizer_A hp h76 (fun x hx => (hRle hx).1)
      (fun x hx => (hRle hx).2) hR hRcard
  have h3L : 3 ≤ CFSG.Open.pRank p c.L := by
    have hle := h.pRank_M_le_pRank_L_add_one (p := p) hp2 hpA hC
    omega
  have h3Lbar : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup c.Lbar) := by
    rw [Counterexample4.pRank_lbar c hp2]
    exact h3L
  have hcontra_cent : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) →
      False := by
    intro h2
    have h2L : 2 ≤ CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) := by
      rw [hcentA]
      exact h2
    have h2M : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (h.A : Set G)) := by
      have hle : c.L ⊓ Subgroup.centralizer (h.A : Set G) ≤
          c.S.M ⊓ Subgroup.centralizer (h.A : Set G) := inf_le_inf c.hyp81.1 le_rfl
      exact h2L.trans (CFSG.SectionRank.pRank_mono hp.1.1.one_lt hle)
    omega
  by_cases hminus : p ∣ qMinusPi r f
  · exact hcontra_cent (hK.1 hminus)
  by_cases hplus : p ∣ qPlusPi r f
  · have hKplus := hK.2.1 hplus
    rcases fam with _ | _ | _ | _ | _ | _
    ·
      obtain ⟨hnotdvdA, hdvdXbar, hrank3⟩ := hKplus.2.2.1 (Or.inl rfl)
      have hL3 : CFSG.Open.pRank p c.L ≤ 3 := by
        rw [← Counterexample4.pRank_lbar c hp2]
        exact hrank3
      by_cases hdvdM : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)
      ·
        obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(c.S.M ⊓ Subgroup.centralizer (h.A : Set G))) p hdvdM
        let y : G := y₀
        have hyM : y ∈ c.S.M := y₀.2.1
        have hyA : y ∈ Subgroup.centralizer (h.A : Set G) := y₀.2.2
        have hyp : orderOf y = p := by
          rw [show orderOf (y₀ : G) = p from by rw [Subgroup.orderOf_coe]; exact hy₀]
        have hyL : y ∉ c.L := by
          intro hyL
          have hmem : y ∈ c.L ⊓ Subgroup.centralizer (h.A : Set G) := ⟨hyL, hyA⟩
          have hpd : p ∣ Nat.card
              (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) := by
            have hz : p ∣ Nat.card (Subgroup.zpowers y) := by
              simpa [Nat.card_zpowers, hyp] using dvd_rfl
            exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem))
          exact hnotdvdA (hCA_dvd.mp hpd)
        refine h.false_of_pElement_not_mem_L hp h76 hyM hyA hyp hyL ?_
        intro X hXA hXcard
        have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
        have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
          rw [h.card_map_of_le_A hXA, hXcard]
        exact (Counterexample4.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num)
          (p := p) hp2 (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)).mpr
          (hdvdXbar _ hXbar_le hXbar_card)
      ·
        have hle := h.pRank_M_le_pRank_L_of_not_dvd (p := p) hpA hdvdM
        omega
    ·
      obtain ⟨hnotdvdA, hdvdXbar, hrank3⟩ := hKplus.2.2.1 (Or.inr rfl)
      have hL3 : CFSG.Open.pRank p c.L ≤ 3 := by
        rw [← Counterexample4.pRank_lbar c hp2]
        exact hrank3
      by_cases hdvdM : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)
      · obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(c.S.M ⊓ Subgroup.centralizer (h.A : Set G))) p hdvdM
        let y : G := y₀
        have hyM : y ∈ c.S.M := y₀.2.1
        have hyA : y ∈ Subgroup.centralizer (h.A : Set G) := y₀.2.2
        have hyp : orderOf y = p := by
          rw [show orderOf (y₀ : G) = p from by rw [Subgroup.orderOf_coe]; exact hy₀]
        have hyL : y ∉ c.L := by
          intro hyL
          have hmem : y ∈ c.L ⊓ Subgroup.centralizer (h.A : Set G) := ⟨hyL, hyA⟩
          have hpd : p ∣ Nat.card
              (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) := by
            have hz : p ∣ Nat.card (Subgroup.zpowers y) := by
              simpa [Nat.card_zpowers, hyp] using dvd_rfl
            exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem))
          exact hnotdvdA (hCA_dvd.mp hpd)
        refine h.false_of_pElement_not_mem_L hp h76 hyM hyA hyp hyL ?_
        intro X hXA hXcard
        have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
        have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
          rw [h.card_map_of_le_A hXA, hXcard]
        exact (Counterexample4.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num)
          (p := p) hp2 (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)).mpr
          (hdvdXbar _ hXbar_le hXbar_card)
      · have hle := h.pRank_M_le_pRank_L_of_not_dvd (p := p) hpA hdvdM
        omega
    ·
      obtain ⟨y, hy, hyp, hu⟩ := hKplus.2.2.2 rfl
      have hpdAbar : p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
        have hz : p ∣ Nat.card (Subgroup.zpowers y) := by
          simpa [Nat.card_zpowers, hyp] using dvd_rfl
        exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy))
      have hpdL : p ∣ Nat.card
          (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) := hCA_dvd.mpr hpdAbar
      obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) p hpdL
      have hzord : orderOf ((z₀ : ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) : G) = p := by
        rw [Subgroup.orderOf_coe]
        exact hz₀
      have h1A : 1 ≤ CFSG.Open.pRank p
          (c.S.M ⊓ Subgroup.centralizer (h.A : Set G)) := by
        refine CFSG.SectionRank.le_pRank (E := Subgroup.zpowers ((z₀ :
          ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) : G)) hp.1.1.one_lt ?_ ?_ ?_
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨c.hyp81.1 z₀.2.1, z₀.2.2⟩)
        · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hzord]; exact pow_orderOf_eq_one _)
        · rw [Nat.card_zpowers, hzord, pow_one]
      have hcentE : ∀ E : Subgroup G, E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
          Nat.card E = 9 →
          0 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) := by
        intro E hEA _ _
        have hle : c.S.M ⊓ Subgroup.centralizer (h.A : Set G) ≤
            c.S.M ⊓ Subgroup.centralizer (E : Set G) :=
          inf_le_inf le_rfl (Subgroup.centralizer_le (fun x hx => hEA hx))
        have h1 := h1A.trans (CFSG.SectionRank.pRank_mono hp.1.1.one_lt hle)
        omega
      have hNX : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
          1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) := by
        intro X hXA hXcard
        have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
        have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
          rw [h.card_map_of_le_A hXA, hXcard]
        obtain ⟨u, huC, huord, huy, hunot⟩ := hu _ hXbar_le hXbar_card
        have hyC : y ∈ Subgroup.centralizer
            (((X.subgroupOf c.L).map π) : Set c.Lbar) :=
          Subgroup.centralizer_le (fun z hz => hXbar_le hz) hy
        have h2bar : 2 ≤ CFSG.Open.pRank p
            (Subgroup.centralizer (((X.subgroupOf c.L).map π) : Set c.Lbar)) :=
          CFSG.GroupTheory.two_le_pRank_of_commute hyC huC hyp huord huy.symm hunot
        have h2L : 2 ≤ CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (X : Set G)) := by
          rw [hcentX X hXA hXcard]
          exact h2bar
        have hle : c.L ⊓ Subgroup.centralizer (X : Set G) ≤
            c.S.M ⊓ Subgroup.normalizer (X : Set G) :=
          inf_le_inf c.hyp81.1 (Subgroup.centralizer_le_normalizer (X : Set G))
        have h2 := h2L.trans (CFSG.SectionRank.pRank_mono hp.1.1.one_lt hle)
        omega
      have hN : ∀ E X : Subgroup G, X ≤ E → E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
          Nat.card E = 9 → Nat.card X = 3 →
          1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) := by
        intro E X hXE hEA _ _ hXcard
        exact hNX X (hXE.trans hEA) hXcard
      have hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
          p ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
        intro X hXA hXcard
        have h2 := hNX X hXA hXcard
        have hpos : 1 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) := by
          omega
        exact (CFSG.GroupTheory.dvd_card_of_one_le_pRank hp.1.1 hpos).trans
          (Subgroup.card_dvd_of_le inf_le_right)
      exact h.false_of_rank_conditions hp h76 hcentE hN hdvd
    ·
      have h2 := hKplus.2.1 rfl
      omega
    ·
      exact hcontra_cent (hKplus.1 (Or.inl rfl))
    ·
      exact hcontra_cent (hKplus.1 (Or.inr rfl))
  ·
    have hnotr : ¬ p ∣ r ^ f := by
      intro hd
      exact hpr ((Nat.prime_dvd_prime_iff_eq hp.1.1 hrprime).mp
        (hp.1.1.dvd_of_dvd_pow hd))
    have hnotprod : ¬ p ∣ r ^ f * (r ^ (2 * f) - 1) := by
      intro hd
      rcases hp.1.1.dvd_mul.mp hd with h | h
      · exact hnotr h
      · rw [pow_two_mul_sub_one_eq r f hrpos] at h
        rcases hp.1.1.dvd_mul.mp h with h' | h'
        · exact hminus h'
        · exact hplus h'
    have h2 := hK.2.2 hnotprod
    omega

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
