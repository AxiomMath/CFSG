module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneMechanisms
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K7 LieFam811 IsLie811 qPlusPi qMinusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

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

private lemma exists_prime_ge_five_dvd_qPlusPi {f : ℕ} (hf : 2 ≤ f)
    (hmod : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ qPlusPi 2 f := by
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have heven : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hn : 3 ≤ qPlusPi 2 f ∧ ¬ 2 ∣ qPlusPi 2 f ∧ ¬ 3 ∣ qPlusPi 2 f := by
    unfold qPlusPi
    generalize 2 ^ f = q at *
    split_ifs <;> omega
  obtain ⟨h3, h2, h3'⟩ := hn
  generalize qPlusPi 2 f = n at *
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hd : n.minFac ∣ n := Nat.minFac_dvd n
  refine ⟨n.minFac, hp, ?_, hd⟩
  have hne2 : n.minFac ≠ 2 := fun h => h2 (h ▸ hd)
  have hne3 : n.minFac ≠ 3 := fun h => h3' (h ▸ hd)
  exact Nat.Prime.five_le_of_ne_two_of_ne_three hp hne2 hne3

private lemma one_le_of_isLie811 {Y : Type} [Group Y] {fam : LieFam811} {r f : ℕ}
    (h : IsLie811 Y fam r f) : 1 ≤ f := by
  obtain ⟨-, -, hfam⟩ := h
  rcases fam with _ | _ | _ | _ | _ | _
  · obtain ⟨-, -, hm⟩ := hfam
    exact hm.admissible.2.1
  · obtain ⟨-, -, -, hm⟩ := hfam
    exact hm.admissible.2.1
  · obtain ⟨-, -, hm⟩ := hfam
    exact hm.admissible.2.1
  · obtain ⟨-, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact hm.admissible.2.1
  · obtain ⟨-, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact hm.admissible.2.1
  · obtain ⟨-, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hfam <;> exact hm.admissible.2.1

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem pRank_inf_centralizer_le_one (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : Conclusion76 D.M p) :
    CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (h.A : Set G)) ≤ 1 := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (h.A : Set G)) := by omega
  obtain ⟨R, hRle, hR, hRcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p) hp_prime (k := 2) h2
  exact h.false_of_le_centralizer_A hp h76 (fun x hx => (hRle hx).1)
    (fun x hx => (hRle hx).2) hR hRcard

theorem pRank_centralizer_Abar_le_one (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : Conclusion76 D.M p) :
    CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) ≤ 1 := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  have hcentA : CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Ctx82E3.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  have hle : c.L ⊓ Subgroup.centralizer (h.A : Set G) ≤
      D.M ⊓ Subgroup.centralizer (h.A : Set G) := inf_le_inf c.hyp81.1 le_rfl
  rw [← hcentA]
  exact (CFSG.SectionRank.pRank_mono hp_prime.one_lt hle).trans
    (h.pRank_inf_centralizer_le_one hp h76)

theorem false_of_mechanismU (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : Conclusion76 D.M p)
    (hdvdM : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G))
    (hnotdvdA : ¬ p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)))
    (hdvdXbar : ∀ X : Subgroup c.Lbar, X ≤ h.Abar → Nat.card X = 3 →
      p ∣ Nat.card (Subgroup.centralizer (X : Set c.Lbar))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hCA_dvd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(D.M ⊓ Subgroup.centralizer (h.A : Set G))) p hdvdM
  let y : G := y₀
  have hyM : y ∈ D.M := y₀.2.1
  have hyA : y ∈ Subgroup.centralizer (h.A : Set G) := y₀.2.2
  have hyp : orderOf y = p := by
    rw [show orderOf (y₀ : G) = p from by rw [Subgroup.orderOf_coe]; exact hy₀]
  have hyL : y ∉ c.L := by
    intro hyL
    have hmem : y ∈ c.L ⊓ Subgroup.centralizer (h.A : Set G) := ⟨hyL, hyA⟩
    have hpd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) := by
      have hz : p ∣ Nat.card (Subgroup.zpowers y) := by
        simpa [Nat.card_zpowers, hyp] using dvd_rfl
      exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem))
    exact hnotdvdA (hCA_dvd.mp hpd)
  refine h.false_of_pElement_not_mem_L hp h76 hyM hyA hyp hyL ?_
  intro X hXA hXcard
  have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
  have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
    rw [h.card_map_of_le_A hXA, hXcard]
  exact (Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num)
    (p := p) hp2 (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)).mpr
    (hdvdXbar _ hXbar_le hXbar_card)

theorem false_of_pomega8m (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (h76 : Conclusion76 D.M p)
    (hK : ∃ y ∈ Subgroup.centralizer (h.Abar : Set c.Lbar), orderOf y = p ∧
      ∀ X : Subgroup c.Lbar, X ≤ h.Abar → Nat.card X = 3 →
        ∃ u ∈ Subgroup.centralizer (X : Set c.Lbar), orderOf u = p ∧ u * y = y * u ∧
          u ∉ Subgroup.zpowers y) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hcentA : CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (h.A : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Ctx82E3.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  have hCA_dvd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  have hcentX : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (X : Set G)) =
        CFSG.Open.pRank p (Subgroup.centralizer
          (((X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) :
            Set c.Lbar)) :=
    fun X hXA _ => Ctx82E3.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
      (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)
  obtain ⟨y, hy, hyp, hu⟩ := hK
  have hpdAbar : p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    have hz : p ∣ Nat.card (Subgroup.zpowers y) := by
      simpa [Nat.card_zpowers, hyp] using dvd_rfl
    exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy))
  have hpdL : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) :=
    hCA_dvd.mpr hpdAbar
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) p hpdL
  have hzord : orderOf ((z₀ : ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hz₀
  have h1A : 1 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (h.A : Set G)) := by
    refine CFSG.SectionRank.le_pRank (E := Subgroup.zpowers ((z₀ :
      ↥(c.L ⊓ Subgroup.centralizer (h.A : Set G))) : G)) hp_prime.one_lt ?_ ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨c.hyp81.1 z₀.2.1, z₀.2.2⟩)
    · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hzord]; exact pow_orderOf_eq_one _)
    · rw [Nat.card_zpowers, hzord, pow_one]
  have hcentE : ∀ E : Subgroup G, E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → 0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
    intro E hEA _ _
    have hle : D.M ⊓ Subgroup.centralizer (h.A : Set G) ≤
        D.M ⊓ Subgroup.centralizer (E : Set G) :=
      inf_le_inf le_rfl (Subgroup.centralizer_le (fun x hx => hEA hx))
    have h1 := h1A.trans (CFSG.SectionRank.pRank_mono hp_prime.one_lt hle)
    omega
  have hNX : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
    intro X hXA hXcard
    have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
    have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
      rw [h.card_map_of_le_A hXA, hXcard]
    obtain ⟨u, huC, huord, huy, hunot⟩ := hu _ hXbar_le hXbar_card
    have hyC : y ∈ Subgroup.centralizer (((X.subgroupOf c.L).map π) : Set c.Lbar) :=
      Subgroup.centralizer_le (fun z hz => hXbar_le hz) hy
    have h2bar : 2 ≤ CFSG.Open.pRank p
        (Subgroup.centralizer (((X.subgroupOf c.L).map π) : Set c.Lbar)) :=
      CFSG.GroupTheory.two_le_pRank_of_commute hyC huC hyp huord huy.symm hunot
    have h2L : 2 ≤ CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [hcentX X hXA hXcard]
      exact h2bar
    have hle : c.L ⊓ Subgroup.centralizer (X : Set G) ≤
        D.M ⊓ Subgroup.normalizer (X : Set G) :=
      inf_le_inf c.hyp81.1 (Subgroup.centralizer_le_normalizer (X : Set G))
    have h2 := h2L.trans (CFSG.SectionRank.pRank_mono hp_prime.one_lt hle)
    omega
  have hN : ∀ E X : Subgroup G, X ≤ E → E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
    intro E X hXE hEA _ _ hXcard
    exact hNX X (hXE.trans hEA) hXcard
  have hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
    intro X hXA hXcard
    have h2 := hNX X hXA hXcard
    have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
      omega
    exact (CFSG.GroupTheory.dvd_card_of_one_le_pRank hp_prime hpos).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  exact h.false_of_rank_conditions hp h76 hcentE hN hdvd

@[expose] def Lie3Survivor (h : Case811Sylow c) (fam : LieFam811) (f p : ℕ) : Prop :=
  (fam = .psp6 ∧ p ∣ qPlusPi 2 f ∧
      ¬ p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)) ∨
  (fam = .l6 ∧ f = 1 ∧ p = 7)

theorem lie3Survivor_of_ne_char (h : Case811Sylow c) (hK7 : K7)
    (hN2 : LieL67PlusRank) (hN3 : K7cSharp) (hN4 : K7L67TwoSharp) (hN5 : K7L4Mech)
    (hN6 : K7L7TwoMech) {fam : LieFam811} {f : ℕ} (hlie : IsLie811 c.Lbar fam 2 f) {p : ℕ}
    (hp : p ∈ D.sig) (h76 : Conclusion76 D.M p)
    (hpA : ∀ g ∈ D.M ⊓ Subgroup.normalizer (h.A : Set G), IsPGroup p (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (h.A : Set G)) :
    h.Lie3Survivor fam f p := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  have hM3 : CFSG.Open.pRank p D.M = 3 := c.pRank_eq_three_of_mem_sigma hp
  have hbar := Ctx82E3.pRank_lbar c hp2
  have hq3 : ¬ 3 ∣ 2 ^ f := fun hd => absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  have hmod : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by omega
  have hC : CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (h.A : Set G)) ≤ 1 :=
    h.pRank_inf_centralizer_le_one hp h76
  have hCbar : CFSG.Open.pRank p (Subgroup.centralizer (h.Abar : Set c.Lbar)) ≤ 1 :=
    h.pRank_centralizer_Abar_le_one hp h76
  have h2Lbar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup c.Lbar) := by
    have hle := h.pRank_M_le_pRank_L_add_one (p := p) hp2 hpA hC
    omega
  by_cases hl67 : fam = .l6 ∨ fam = .l7
  ·
    by_cases hf2 : 2 ≤ f
    ·
      exfalso
      obtain ⟨p', hp'prime, hp'5, hp'dvd⟩ := exists_prime_ge_five_dvd_qPlusPi hf2 hmod
      haveI : Fact p'.Prime := ⟨hp'prime⟩
      have hp'2 : p' ≠ 2 := by omega
      have h4 := hN2 c.Lbar fam f hl67 hlie p' hp'prime hp'5 hp'dvd
      simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4
      have h4' := Ctx82E3.pRank_lbar c hp'2
      have h5 : CFSG.Open.pRank p' c.L ≤ CFSG.Open.pRank p' D.M :=
        CFSG.SectionRank.pRank_mono hp'prime.one_lt c.hyp81.1
      have h6 := c.pRank_le_three hp'prime hp'2
      omega
    ·
      have hf : f = 1 := by
        have := one_le_of_isLie811 hlie
        omega
      subst hf
      have hp7 : p = 7 := by
        by_contra hne
        have h1 := hN4 c.Lbar fam hl67 hlie p hp_prime hp5 hne
        simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
        omega
      rcases hl67 with rfl | rfl
      · exact Or.inr ⟨rfl, rfl, hp7⟩
      ·
        exfalso
        subst hp7
        obtain ⟨hnotdvdA, hdvdXbar⟩ := hN6 c.Lbar hlie h.Abar h.isElemAbelian_Abar h.card_Abar
        by_cases hdvdM : 7 ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)
        · exact h.false_of_mechanismU hp h76 hdvdM hnotdvdA hdvdXbar
        · have hle := h.pRank_M_le_pRank_L_of_not_dvd (p := 7) hpA hdvdM
          have hK := hK7 c.Lbar .l7 2 1 hlie 7 hp_prime hp5 hp2 h.Abar h.isElemAbelian_Abar
            h.card_Abar
          simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at hK
          have h2 := hK.2.2 (by norm_num)
          omega
  ·
    have hfam : fam = .psp6 ∨ fam = .pomega8m ∨ fam = .l4 := by
      rcases fam with _ | _ | _ | _ | _ | _
      · exact Or.inl rfl
      · exact absurd hlie.2.2.2.1 (by norm_num)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd (Or.inl rfl) hl67
      · exact absurd (Or.inr rfl) hl67
    have hK := hK7 c.Lbar fam 2 f hlie p hp_prime hp5 hp2 h.Abar h.isElemAbelian_Abar
      h.card_Abar
    simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at hK
    by_cases hminus : p ∣ qMinusPi 2 f
    ·
      exfalso
      have h2 := hK.1 hminus
      omega
    by_cases hplus : p ∣ qPlusPi 2 f
    · have hKplus := hK.2.1 hplus
      rcases hfam with rfl | rfl | rfl
      ·
        obtain ⟨hnotdvdA, hdvdXbar, -⟩ := hKplus.2.2.1 (Or.inl rfl)
        by_cases hdvdM : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)
        · exact (h.false_of_mechanismU hp h76 hdvdM hnotdvdA hdvdXbar).elim
        · exact Or.inl ⟨rfl, hplus, hdvdM⟩
      ·
        exact (h.false_of_pomega8m hp h76 (hKplus.2.2.2 rfl)).elim
      ·
        exfalso
        by_cases hdvdM : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)
        · obtain ⟨hnotdvdA, hdvdXbar⟩ := hN5 c.Lbar f hlie p hp_prime hp5 hplus h.Abar
            h.isElemAbelian_Abar h.card_Abar
          exact h.false_of_mechanismU hp h76 hdvdM hnotdvdA hdvdXbar
        · have hle := h.pRank_M_le_pRank_L_of_not_dvd (p := p) hpA hdvdM
          have h2 := hKplus.2.1 rfl
          omega
    ·
      exfalso
      have hnotr : ¬ p ∣ 2 ^ f := by
        intro hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp
          (hp_prime.dvd_of_dvd_pow hd))
      have hnotprod : ¬ p ∣ 2 ^ f * (2 ^ (2 * f) - 1) := by
        intro hd
        rcases hp_prime.dvd_mul.mp hd with h' | h'
        · exact hnotr h'
        · rw [pow_two_mul_sub_one_eq 2 f (by norm_num)] at h'
          rcases hp_prime.dvd_mul.mp h' with h'' | h''
          · exact hminus h''
          · exact hplus h''
      have h1 := hN3 c.Lbar fam f hfam hlie p hp_prime hp5 hnotprod
      simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
      omega

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
