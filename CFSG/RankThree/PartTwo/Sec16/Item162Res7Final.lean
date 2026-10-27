module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7Elts
import CFSG.RankThree.PartTwo.Sec16.Item162Res7Dich
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abOPrime
import CFSG.Quasithin.Background.A4V
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise commutatorElement

namespace Res162Seven

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G} {b : G} {Lb : Subgroup G}

namespace Conf683

private theorem odd_orderOf_of_pow_three {j : G} (hj : ∃ k : ℕ, j ^ 3 ^ k = 1) :
    Odd (orderOf j) := by
  obtain ⟨k, hk⟩ := hj
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow (p := 3) (m := k) Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one hk)
  rw [hm]
  exact (show Odd (3 : ℕ) by norm_num [Odd]).pow (n := m)

private theorem omegaOneCenterOf_le_thompsonJ (S : Subgroup G) :
    Quasithin.omegaOneCenterOf S ≤ Quasithin.thompsonJ S := by
  intro z hz
  exact CFSG.QuasithinUnique.GammaExtra.mem_thompsonJ_of_central_involution
    (CFSG.Quasithin.A4.omegaOneCenterOf_le S hz)
    (fun s hs => Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.A4.centerOf_le_centralizer S
        (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf S hz)) s hs)
    (CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hz)

private theorem oPrimeResidualOf_three_le_of_forall {X H : Subgroup G}
    (h : ∀ x ∈ X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ H) :
    oPrimeResidualOf 3 X ≤ H := by
  rw [CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.oPrimeResidualOf_eq_closure' 3 X]
  exact (Subgroup.closure_le H).mpr fun x hx => h x hx.1 hx.2

private theorem oPrimeResidualOf_three_le_of_sup {K D P : Subgroup G}
    (hDK : D ≤ K) (hPK : P ≤ K) (hKDP : K ≤ D ⊔ P)
    (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G)) (hP2 : IsPGroup 2 P) :
    oPrimeResidualOf 3 K ≤ D := by
  classical
  let Dk : Subgroup ↥K := D.subgroupOf K
  haveI hDkNormal : Dk.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).mpr hKD
  apply oPrimeResidualOf_three_le_of_forall
  intro x hxK hx3
  obtain ⟨k, hkx⟩ := hx3
  have hxDP : x ∈ ((D ⊔ P : Subgroup G) : Set G) := hKDP hxK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D P hDP] at hxDP
  obtain ⟨d, hdD, p, hpP, hdp⟩ := hxDP
  let π : ↥K →* (↥K ⧸ Dk) := QuotientGroup.mk' Dk
  have hxd : π ⟨x, hxK⟩ = π ⟨p, hPK hpP⟩ := by
    have hx_eq : (⟨x, hxK⟩ : ↥K) = ⟨d, hDK hdD⟩ * ⟨p, hPK hpP⟩ := Subtype.ext hdp.symm
    have hdDk : (⟨d, hDK hdD⟩ : ↥K) ∈ Dk := hdD
    have hd1 : π ⟨d, hDK hdD⟩ = 1 := by
      change ((⟨d, hDK hdD⟩ : ↥K) : ↥K ⧸ Dk) = 1
      exact (QuotientGroup.eq_one_iff _).mpr hdDk
    calc π ⟨x, hxK⟩ = π (⟨d, hDK hdD⟩ * ⟨p, hPK hpP⟩) := by rw [hx_eq]
      _ = π ⟨d, hDK hdD⟩ * π ⟨p, hPK hpP⟩ := map_mul _ _ _
      _ = π ⟨p, hPK hpP⟩ := by rw [hd1, one_mul]
  have hdvd3 : orderOf (π ⟨x, hxK⟩) ∣ 3 ^ k := by
    have h1 : (⟨x, hxK⟩ : ↥K) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hkx)
    exact (orderOf_map_dvd π _).trans (orderOf_dvd_of_pow_eq_one h1)
  obtain ⟨m, hm⟩ := hP2 ⟨p, hpP⟩
  have hp2 : (⟨p, hPK hpP⟩ : ↥K) ^ 2 ^ m = 1 := by
    apply Subtype.ext
    change p ^ 2 ^ m = 1
    simpa using congrArg Subtype.val hm
  have hdvd2 : orderOf (π ⟨x, hxK⟩) ∣ 2 ^ m := by
    rw [hxd]
    exact (orderOf_map_dvd π _).trans (orderOf_dvd_of_pow_eq_one hp2)
  have hcop : Nat.Coprime (3 ^ k) (2 ^ m) := (by decide : Nat.Coprime 3 2).pow k m
  have h1 : orderOf (π ⟨x, hxK⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
  have h2 : π ⟨x, hxK⟩ = 1 := orderOf_eq_one_iff.mp h1
  have h3 : (⟨x, hxK⟩ : ↥K) ∈ Dk := by
    change ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ Dk) = 1 at h2
    exact (QuotientGroup.eq_one_iff _).mp h2
  exact Subgroup.mem_subgroupOf.mp h3

private theorem inf_le_zpowers_of_le_pCoreOf (h : Conf683 A c L Y₁ Y₂ S b Lb)
    (hY₂N₁ : Y₂ ≤ Subgroup.normalizer (Y₁ : Set G))
    (hY₁N₂ : Y₁ ≤ Subgroup.normalizer (Y₂ : Set G))
    (hDP : Y₁ ⊓ Y₂ ≤ CFSG.Open.pCoreOf 2 Y₂) :
    (A ⊓ Y₁ : Subgroup G) ≤ Subgroup.zpowers b := by
  have hsec : (A ⊓ Y₁ : Subgroup G) ≤
      Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) := by
    rintro a ⟨haA, haY₁⟩
    refine ⟨haA, fun y hy => ?_⟩
    have h1 : a * y * a⁻¹ ∈ Y₂ :=
      (Subgroup.mem_normalizer_iff.mp (hY₁N₂ haY₁) y).mp hy
    have h2 : a * y * a⁻¹ * y⁻¹ ∈ Y₂ := Y₂.mul_mem h1 (Y₂.inv_mem hy)
    have h3 : y * a⁻¹ * y⁻¹ ∈ Y₁ :=
      (Subgroup.mem_normalizer_iff.mp (hY₂N₁ hy) a⁻¹).mp (Y₁.inv_mem haY₁)
    have h4 : a * y * a⁻¹ * y⁻¹ ∈ Y₁ := by
      have := Y₁.mul_mem haY₁ h3
      simpa [mul_assoc] using this
    exact hDP (Subgroup.mem_inf.mpr ⟨h4, h2⟩)
  intro a ha
  have hmem := hsec ha
  rwa [h.sc₂] at hmem

theorem le_normalizer_thompsonJ₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Y₁ ⊔ S ≤ Subgroup.normalizer (Quasithin.thompsonJ S : Set G) := by
  classical
  let Z : Subgroup G := Quasithin.omegaOneCenterOf S
  let Q₁ : Subgroup G := CFSG.Open.pCoreOf 2 (Y₁ ⊔ S)
  obtain ⟨g, hg⟩ := exists_map_S₁ h
  obtain ⟨t, -, htA, htS, -, htb, htinv⟩ := exists_t₂ h
  obtain ⟨htK, htoddt⟩ := a7Rep_not_mem₁ h (Classical.choice h.a7₁) htA htS htb htinv
  have hb_ord : orderOf b = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  have hZCS : Z ≤ Subgroup.centralizer (S : Set G) :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf S).trans
      (CFSG.Quasithin.A4.centerOf_le_centralizer S)
  have hZCQ : Z ≤ Subgroup.centralizer (Q₁ : Set G) :=
    hZCS.trans (Subgroup.centralizer_le (pCoreOf_sup_le₁ h))
  have hZQ₁ : Z ≤ Q₁ :=
    (le_inf ((CFSG.Quasithin.A4.omegaOneCenterOf_le S).trans le_sup_right) hZCQ).trans
      (centralizer_Q_le h)
  have hZ_U : Z ≤ Quasithin.omegaOneCenterOf Q₁ := by
    intro z hz
    refine Subgroup.subset_closure ?_
    exact ⟨⟨hZQ₁ hz, hZCQ hz⟩,
      CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hz⟩
  have hZne' : Quasithin.omegaOneCenterOf S ≠ ⊥ := by
    intro hbot
    have h4 := four_le_card_omegaOneCenterOf h
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hZne : Z ≠ ⊥ := hZne'
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
  obtain ⟨u, hu1⟩ := exists_ne (1 : ↥Z)
  have huU : (u : G) ∈ Quasithin.omegaOneCenterOf Q₁ := hZ_U u.2
  have hune : b * (u : G) * b⁻¹ * (u : G)⁻¹ ≠ 1 := by
    intro h1
    have huC : (u : G) ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : b * (u : G) * b⁻¹ = (u : G) := mul_inv_eq_one.mp h1
      calc (u : G) * b = (b * (u : G) * b⁻¹) * b := by rw [h2]
        _ = b * (u : G) := by group
    have hbot : (u : G) ∈ (⊥ : Subgroup G) := by
      rw [← omegaOneCenterOf_inf_centralizer_eq_bot h]
      exact ⟨u.2, huC⟩
    rw [Subgroup.mem_bot] at hbot
    exact hu1 (Subtype.ext hbot)
  have hJ := le_normalizer_thompsonJ_of_a7 (K := Y₁) (S := S)
    (isPGroup_S₁ h) h.maxCE.1.s₁.prop.1.2 (pCoreOf_sup_le₁ h)
    (Classical.choice h.a7₁) (le_of_eq hg) htK htS htoddt (b_mem_y₁ h)
    (by rw [hb_ord]; exact ⟨1, by norm_num⟩) ⟨(u : G), huU, hune⟩
  exact (show Y₁ ⊔ S ≤ Y₁ ⊔ S ⊔ Subgroup.zpowers t from le_sup_left).trans hJ

private theorem eq_of_not_le_pCoreOf (h : Conf683 A c L Y₁ Y₂ S b Lb)
    {D P : Subgroup G} (hD : D = Y₁ ⊓ Y₂) (hP : P = CFSG.Open.pCoreOf 2 Y₂)
    (hDN : Y₂ ≤ Subgroup.normalizer (D : Set G)) (hDP : ¬ D ≤ P) : Y₁ = Y₂ := by
  classical
  obtain ⟨e⟩ := h.a7₂
  let Pk : Subgroup ↥Y₂ := CFSG.pCore 2 ↥Y₂
  let Dk : Subgroup ↥Y₂ := D.subgroupOf Y₂
  have hDY₂ : D ≤ Y₂ := (le_of_eq hD).trans inf_le_right
  have hDY₁ : D ≤ Y₁ := (le_of_eq hD).trans inf_le_left
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂) := e.isSimpleGroup
  have hDkNormal : Dk.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY₂).mpr hDN
  haveI : (Dk.map (QuotientGroup.mk' Pk)).Normal :=
    hDkNormal.map _ (QuotientGroup.mk'_surjective Pk)
  have himg_ne : Dk.map (QuotientGroup.mk' Pk) ≠ ⊥ := by
    intro hbot
    apply hDP
    intro d hdD
    have hdY : d ∈ Y₂ := hDY₂ hdD
    have hmem : QuotientGroup.mk' Pk (⟨d, hdY⟩ : ↥Y₂) ∈ Dk.map (QuotientGroup.mk' Pk) :=
      Subgroup.mem_map_of_mem _ (show (⟨d, hdY⟩ : ↥Y₂) ∈ Dk from hdD)
    rw [hbot] at hmem
    have h1 : QuotientGroup.mk' Pk (⟨d, hdY⟩ : ↥Y₂) = 1 := Subgroup.mem_bot.mp hmem
    have hdP : d ∈ CFSG.Open.pCoreOf 2 Y₂ :=
      (CFSG.mem_openPCoreOf_iff (H := Y₂) (⟨d, hdY⟩ : ↥Y₂)).mpr
        ((QuotientGroup.eq_one_iff _).mp h1)
    rwa [← hP] at hdP
  have hDkTop : Dk.map (QuotientGroup.mk' Pk) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Dk.map (QuotientGroup.mk' Pk)) with
      hbot | htop
    · exact absurd hbot himg_ne
    · exact htop
  have hY₂DP : Y₂ ≤ D ⊔ P := by
    intro y hy
    have hq : QuotientGroup.mk' Pk (⟨y, hy⟩ : ↥Y₂) ∈ Dk.map (QuotientGroup.mk' Pk) := by
      rw [hDkTop]
      exact Subgroup.mem_top _
    obtain ⟨d, hdDk, hdeq⟩ := Subgroup.mem_map.mp hq
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hdDk
    have hdY : (d : G) ∈ Y₂ := hDY₂ hdD
    have hmem : (d⁻¹ * ⟨y, hy⟩ : ↥Y₂) ∈ Pk := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change QuotientGroup.mk' Pk (d⁻¹ * ⟨y, hy⟩) = 1
      rw [map_mul, map_inv, hdeq, inv_mul_cancel]
    have hmemP : (d : G)⁻¹ * y ∈ P := by
      have hmem' := (CFSG.mem_openPCoreOf_iff (H := Y₂) (d⁻¹ * ⟨y, hy⟩)).mpr hmem
      rwa [← hP] at hmem'
    have hy_eq : y = (d : G) * ((d : G)⁻¹ * y) := by group
    rw [hy_eq]
    exact (D ⊔ P).mul_mem (Subgroup.mem_sup_left hdD) (Subgroup.mem_sup_right hmemP)
  have hDPN : D ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact hDY₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂)
  have hPK : P ≤ Y₂ := by
    rw [hP]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂
  have hY₂D : Y₂ ≤ D := by
    have hres := oPrimeResidualOf_three_le_of_sup (K := Y₂) (D := D) (P := P)
      hDY₂ hPK hY₂DP hDPN hDN hP2
    exact (le_of_eq h.maxCE.1.mem₂.prop.1.2.1).trans hres
  have hY₂Y₁ : Y₂ ≤ Y₁ := hY₂D.trans hDY₁
  have hY₁Y₂ : Y₁ ≤ Y₂ := h.maxCE.1.mem₂.2 h.maxCE.1.mem₁.prop hY₂Y₁
  exact (le_antisymm hY₂Y₁ hY₁Y₂).symm

theorem not_le_normalizer_thompsonJ₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ¬ Y₂ ≤ Subgroup.normalizer (Quasithin.thompsonJ S : Set G) := by
  classical
  intro hN
  let J : Subgroup G := Quasithin.thompsonJ S
  let M : Subgroup G := Subgroup.normalizer (J : Set G)
  let P : Subgroup G := CFSG.Open.pCoreOf 2 Y₂
  let D : Subgroup G := Y₁ ⊓ Y₂
  have hZJ : Quasithin.omegaOneCenterOf S ≤ J := omegaOneCenterOf_le_thompsonJ S
  have hZne' : Quasithin.omegaOneCenterOf S ≠ ⊥ := by
    intro hbot
    have h4 := four_le_card_omegaOneCenterOf h
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hJne : J ≠ ⊥ := fun hbot =>
    hZne' (le_bot_iff.mp (hZJ.trans (le_of_eq hbot)))
  have hJ2 : IsPGroup 2 J :=
    (isPGroup_S₁ h).to_le (CFSG.QuasithinUnique.GammaExtra.thompsonJ_le_self S)
  have hMlocal : IsPLocal 2 M := ⟨J, hJne, hJ2, rfl⟩
  have hAM : A ≤ M :=
    (h.maxCE.1.s₂.prop.1.1.1.2.2).trans
      (CFSG.QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ S)
  have hY₁M : Y₁ ≤ M :=
    (show Y₁ ≤ Y₁ ⊔ S from le_sup_left).trans (le_normalizer_thompsonJ₁ h)
  have hY₂M : Y₂ ≤ M := hN
  have hMle₁ : M ≤ Subgroup.normalizer (Y₁ : Set G) :=
    le_normalizer_of_isPLocal h.item153 h.claim153Normal h.maxCE.1.mem₁ hMlocal hY₁M hAM
  have hMle₂ : M ≤ Subgroup.normalizer (Y₂ : Set G) :=
    le_normalizer_of_isPLocal h.item153 h.claim153Normal h.maxCE.1.mem₂ hMlocal hY₂M hAM
  have hY₂N₁ : Y₂ ≤ Subgroup.normalizer (Y₁ : Set G) := hY₂M.trans hMle₁
  have hY₁N₂ : Y₁ ≤ Subgroup.normalizer (Y₂ : Set G) := hY₁M.trans hMle₂
  have hDN : Y₂ ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf hY₂N₁ Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Y₁) (K := Y₂))
  by_cases hDP : D ≤ P
  · have hAle := inf_le_zpowers_of_le_pCoreOf h hY₂N₁ hY₁N₂ (by simpa [D, P] using hDP)
    have h9 : Nat.card (A ⊓ Y₁ : Subgroup G) = 9 := (card_inf₁ h).1
    have h3 : Nat.card (Subgroup.zpowers b : Subgroup G) = 3 :=
      (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
    have := Subgroup.card_le_of_le hAle
    omega
  · exact h.ne (eq_of_not_le_pCoreOf h rfl rfl hDN hDP).symm

theorem le_centralizer_omegaOneCenterOf (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Y₂ ⊔ S ≤ Subgroup.centralizer (Quasithin.omegaOneCenterOf S : Set G) := by
  classical
  let Z : Subgroup G := Quasithin.omegaOneCenterOf S
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)
  have hZR : Z ≤ R := omegaOneCenterOf_le_R h
  have hZCS : Z ≤ Subgroup.centralizer (S : Set G) :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf S).trans
      (CFSG.Quasithin.A4.centerOf_le_centralizer S)
  have hZCR : Z ≤ Subgroup.centralizer (R : Set G) :=
    hZCS.trans (Subgroup.centralizer_le (R_le h))
  have hZU : Z ≤ Quasithin.omegaOneCenterOf R := by
    intro z hz
    refine Subgroup.subset_closure ?_
    exact ⟨⟨hZR hz, hZCR hz⟩,
      CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hz⟩
  have hYCU : Y₂ ≤ Subgroup.centralizer (Quasithin.omegaOneCenterOf R : Set G) := by
    rw [h.maxCE.1.mem₂.prop.1.2.1]
    refine oPrimeResidualOf_three_le_of_forall ?_
    intro j hjY₂ hj3
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    by_contra hne
    have hjU : ∃ u ∈ Quasithin.omegaOneCenterOf R, j * u * j⁻¹ * u⁻¹ ≠ 1 := by
      refine ⟨u, hu, ?_⟩
      intro h1
      apply hne
      have h2 : j * u * j⁻¹ = u := mul_inv_eq_one.mp h1
      calc u * j = (j * u * j⁻¹) * j := by rw [h2]
        _ = j * u := by group
    obtain ⟨g, hg⟩ := exists_map_S₂ h
    obtain ⟨t, -, htA, htS, -, htc, htinv⟩ := exists_t₁ h
    obtain ⟨htK, htoddt⟩ := a7Rep_not_mem₂ h (Classical.choice h.a7₂) htA htS htc htinv
    have hJ := le_normalizer_thompsonJ_of_a7 (K := Y₂) (S := S)
      (isPGroup_S₁ h) h.maxCE.1.s₂.prop.1.2 (R_le h) (Classical.choice h.a7₂)
      (le_of_eq hg) htK htS htoddt hjY₂ (odd_orderOf_of_pow_three hj3) hjU
    have hcontra : Y₂ ≤ Subgroup.normalizer (Quasithin.thompsonJ S : Set G) :=
      (show Y₂ ≤ Y₂ ⊔ S from le_sup_left).trans
        ((show Y₂ ⊔ S ≤ Y₂ ⊔ S ⊔ Subgroup.zpowers t from le_sup_left).trans hJ)
    exact not_le_normalizer_thompsonJ₂ h hcontra
  have hY₂CZ : Y₂ ≤ Subgroup.centralizer (Z : Set G) :=
    hYCU.trans (Subgroup.centralizer_le hZU)
  have hSCZ : S ≤ Subgroup.centralizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZCS hz) s hs).symm
  simpa [Z] using sup_le hY₂CZ hSCZ

private theorem map_conj_omegaOneCenterOf_eq (h : Conf683 A c L Y₁ Y₂ S b Lb)
    {y b' : G} (hyKS : y ∈ Y₁ ⊔ S) (hyb : y * b * y⁻¹ ∈ Subgroup.zpowers b')
    (hb'Z : b' ∈ Subgroup.centralizer (Quasithin.omegaOneCenterOf S : Set G)) :
    (Quasithin.omegaOneCenterOf S).map (MulAut.conj y⁻¹).toMonoidHom =
      S ⊓ Subgroup.centralizer ({b} : Set G) := by
  classical
  let Z : Subgroup G := Quasithin.omegaOneCenterOf S
  let V : Subgroup G := S ⊓ Subgroup.centralizer ({b} : Set G)
  have hZJ : Z ≤ Quasithin.thompsonJ S := omegaOneCenterOf_le_thompsonJ S
  have hyinvN : y⁻¹ ∈ Subgroup.normalizer (Quasithin.thompsonJ S : Set G) :=
    le_normalizer_thompsonJ₁ h ((Y₁ ⊔ S).inv_mem hyKS)
  have hV'J : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤ Quasithin.thompsonJ S := by
    have h1 : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤
        (Quasithin.thompsonJ S).map (MulAut.conj y⁻¹).toMonoidHom :=
      Subgroup.map_mono hZJ
    have h2 : (Quasithin.thompsonJ S).map (MulAut.conj y⁻¹).toMonoidHom =
        Quasithin.thompsonJ S := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyinvN
    rwa [h2] at h1
  have hV'S : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤ S :=
    hV'J.trans (CFSG.QuasithinUnique.GammaExtra.thompsonJ_le_self S)
  have hbV' : b ∈ Subgroup.centralizer
      ((Z.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro v ⟨z, hzZ, rfl⟩
    have hyby : y * b * y⁻¹ ∈ Subgroup.centralizer (Z : Set G) :=
      (Subgroup.zpowers_le.mpr hb'Z) hyb
    have hzc : z * (y * b * y⁻¹) = (y * b * y⁻¹) * z :=
      Subgroup.mem_centralizer_iff.mp hyby z hzZ
    show (MulAut.conj y⁻¹) z * b = b * (MulAut.conj y⁻¹) z
    rw [MulAut.conj_apply, inv_inv]
    calc y⁻¹ * z * y * b = y⁻¹ * (z * (y * b * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * b * y⁻¹) * z) * y := by rw [hzc]
      _ = b * (y⁻¹ * z * y) := by group
  have hV'Cb : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({b} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hbV' v hv)
  have hV'V : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤ V := le_inf hV'S hV'Cb
  have hV'card : Nat.card (Z.map (MulAut.conj y⁻¹).toMonoidHom) = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  have hV'ge : Nat.card V ≤ Nat.card (Z.map (MulAut.conj y⁻¹).toMonoidHom) := by
    rw [hV'card, show Nat.card V = 4 from (card_V h).2]
    simpa [Z] using four_le_card_omegaOneCenterOf h
  show Z.map (MulAut.conj y⁻¹).toMonoidHom = V
  exact Subgroup.eq_of_le_of_card_ge hV'V hV'ge

private theorem map_conj_le_centralizer_pCoreOf (h : Conf683 A c L Y₁ Y₂ S b Lb)
    {y : G} (hyNQ : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) : Set G)) :
    (Quasithin.omegaOneCenterOf S).map (MulAut.conj y⁻¹).toMonoidHom ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) : Set G) := by
  classical
  let Z : Subgroup G := Quasithin.omegaOneCenterOf S
  let Q₁ : Subgroup G := CFSG.Open.pCoreOf 2 (Y₁ ⊔ S)
  have hZCS : Z ≤ Subgroup.centralizer (S : Set G) :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf S).trans
      (CFSG.Quasithin.A4.centerOf_le_centralizer S)
  have hQmap : Q₁.map (MulAut.conj y⁻¹).toMonoidHom = Q₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (Q₁ : Set G)).inv_mem hyNQ)
  have h1 : Z.map (MulAut.conj y⁻¹).toMonoidHom ≤
      Subgroup.centralizer ((S.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    refine (Subgroup.map_mono hZCS).trans ?_
    simpa [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (S : Set G)
        (MulAut.conj y⁻¹).toMonoidHom
  refine h1.trans (Subgroup.centralizer_le ?_)
  intro x hx
  refine Subgroup.map_mono (pCoreOf_sup_le₁ h) ?_
  rwa [hQmap]

theorem V_le_centralizer_Q (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    S ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) : Set G) := by
  classical
  let Z : Subgroup G := Quasithin.omegaOneCenterOf S
  obtain ⟨b', -, -, hb'D, -, -⟩ := exists_b' h
  obtain ⟨y₂, hy₂KS, -, -, hy₂b', -⟩ := exists_y₂ h hb'D
  obtain ⟨y, hyKS, -, hyb, -, -⟩ := exists_y₁ h hb'D
  have hcent : Y₂ ⊔ S ≤ Subgroup.centralizer (Z : Set G) :=
    le_centralizer_omegaOneCenterOf h
  have hcZ : c ∈ Subgroup.centralizer (Z : Set G) :=
    hcent (Subgroup.mem_sup_left (c_mem_y₂ h))
  have hy₂Z : y₂ ∈ Subgroup.centralizer (Z : Set G) := hcent hy₂KS
  have hy₂b'C : y₂ * b' * y₂⁻¹ ∈ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.zpowers_le.mpr hcZ) hy₂b'
  have hb'Z : b' ∈ Subgroup.centralizer (Z : Set G) := by
    have hEq : b' = y₂⁻¹ * (y₂ * b' * y₂⁻¹) * y₂ := by group
    rw [hEq]
    exact (Subgroup.centralizer (Z : Set G)).mul_mem
      ((Subgroup.centralizer (Z : Set G)).mul_mem
        ((Subgroup.centralizer (Z : Set G)).inv_mem hy₂Z) hy₂b'C) hy₂Z
  have heq := map_conj_omegaOneCenterOf_eq h hyKS hyb hb'Z
  have hyNQ : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₁ ⊔ S)) hyKS
  have hle := map_conj_le_centralizer_pCoreOf h hyNQ
  rwa [heq] at hle

end Conf683

open Conf683

private theorem c_not_centralizes_pCoreOf_sup (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ w ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S), c * w * c⁻¹ * w⁻¹ ≠ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ w ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S), c * w * c⁻¹ * w⁻¹ = 1 := by
    intro w hw
    by_contra hne
    exact hcon ⟨w, hw, hne⟩
  have hcC : c ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : c * w * c⁻¹ = w := mul_inv_eq_one.mp (hcon' w hw)
    calc w * c = (c * w * c⁻¹) * c := by rw [h1]
      _ = c * w := by group
  have hcYR : c ∈ (Y₂ ⊔ S) ⊓
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) : Set G) :=
    ⟨Subgroup.mem_sup_left (c_mem_y₂ h), hcC⟩
  have hcR : c ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := centralizer_R_le h hcYR
  have hc1 : c = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Y₂ ⊔ S)) (isElemAbelian_A h)
    hcR (c_mem h)
  exact c_ne_one h hc1

private theorem card_le_four_mul_card (h : Conf683 A c L Y₁ Y₂ S b Lb)
    {R R₁ R₂ V X : Subgroup G} (hR : R = CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) (hR₁R : R₁ ≤ R)
    (hV : V = S ⊓ Subgroup.centralizer ({b} : Set G))
    (hRlt : R₂ < R₁) (hX₁ : X ≤ R₁)
    (hX : X = (R₁ ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₂) :
    Nat.card R₁ ≤ 4 * Nat.card X := by
  classical
  let Q₁ : Subgroup G := CFSG.Open.pCoreOf 2 (Y₁ ⊔ S)
  have hQCV : Q₁ ≤ Subgroup.centralizer (V : Set G) := by
    have hqcv := V_le_centralizer_Q h
    rw [← hV] at hqcv
    rwa [Subgroup.le_centralizer_iff] at hqcv
  have hrel0 : ∀ (A B : Subgroup G), A.relIndex B ≠ 0 := by
    intro A B
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h6 : Q₁.relIndex S = 4 := by
    have hrels := Subgroup.relIndex_mul_card (H := Q₁) (K := S)
    rw [inf_of_le_left (pCoreOf_sup_le₁ h)] at hrels
    rw [(push₁ h).2.1] at hrels
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥Q₁)) hrels
  have hXrel : X.relIndex R₁ ≤ 4 := by
    have h1 : X.relIndex R₁ ≤ (R₁ ⊓ Subgroup.centralizer (V : Set G)).relIndex R₁ :=
      Subgroup.relIndex_le_of_le_left
        (show R₁ ⊓ Subgroup.centralizer (V : Set G) ≤ X by rw [hX]; exact le_sup_left)
        (hrel0 _ _)
    have h2 : (R₁ ⊓ Subgroup.centralizer (V : Set G)).relIndex R₁ ≤
        (R₁ ⊓ Q₁).relIndex R₁ :=
      Subgroup.relIndex_le_of_le_left
        (show R₁ ⊓ Q₁ ≤ R₁ ⊓ Subgroup.centralizer (V : Set G) from
          inf_le_inf_left R₁ hQCV) (hrel0 _ _)
    have h3 : (R₁ ⊓ Q₁).relIndex R₁ = Q₁.relIndex R₁ :=
      Subgroup.inf_relIndex_left (H := R₁) (K := Q₁)
    have h4 : Q₁.relIndex R₁ ≤ Q₁.relIndex R :=
      Subgroup.relIndex_le_of_le_right hR₁R (hrel0 Q₁ R)
    have h5 : Q₁.relIndex R ≤ Q₁.relIndex S :=
      Subgroup.relIndex_le_of_le_right (by rw [hR]; exact R_le h) (hrel0 Q₁ S)
    calc X.relIndex R₁ ≤ (R₁ ⊓ Subgroup.centralizer (V : Set G)).relIndex R₁ := h1
      _ ≤ (R₁ ⊓ Q₁).relIndex R₁ := h2
      _ = Q₁.relIndex R₁ := h3
      _ ≤ Q₁.relIndex R := h4
      _ ≤ Q₁.relIndex S := h5
      _ = 4 := h6
  have hcardR₁ : Nat.card R₁ = X.relIndex R₁ * Nat.card X := by
    have hrels := Subgroup.relIndex_mul_card (H := X) (K := R₁)
    rw [inf_of_le_left hX₁] at hrels
    exact hrels.symm
  exact hcardR₁.le.trans (Nat.mul_le_mul_right _ hXrel)

theorem not_conf683 : ¬ Conf683 A c L Y₁ Y₂ S b Lb := by
  classical
  rintro h
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)
  let V : Subgroup G := S ⊓ Subgroup.centralizer ({b} : Set G)
  obtain ⟨g, hg⟩ := exists_map_S₂ h
  obtain ⟨t, -, htA, htS, -, htc, htinv⟩ := exists_t₁ h
  obtain ⟨htK, htoddt⟩ := a7Rep_not_mem₂ h (Classical.choice h.a7₂) htA htS htc htinv
  have hc_ord : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  obtain ⟨R₁, R₂, hRlt, hR₁R, hR₁R₂, -, hNR₂, hFF⟩ :=
    exists_chief_factor_card_lt_of_a7 (K := Y₂) (S := S) (W := R)
      (isPGroup_S₁ h) h.maxCE.1.s₂.prop.1.2 (R_le h) (Classical.choice h.a7₂)
      (le_of_eq hg) htK htS htoddt (le_refl R) (le_normalizer_pCoreOf_sup htK htS)
      (c_mem_y₂ h) (by rw [hc_ord]; exact ⟨1, by norm_num⟩) (c_not_centralizes_pCoreOf_sup h)
  let X : Subgroup G := (R₁ ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₂
  have hVS : V ≤ S := inf_le_left
  have hVne : V ≠ ⊥ := by
    intro hbot
    have h4 : Nat.card V = 4 := (card_V h).2
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hVQ : ¬ V ≤ R := by
    intro hVR
    apply hVne
    rw [eq_bot_iff]
    exact (le_inf le_rfl hVR).trans (le_of_eq (V_inf_R h))
  have hX₂ : R₂ ≤ X := le_sup_right
  have hX₁ : X ≤ R₁ := sup_le inf_le_left hRlt.le
  have hNV : V ≤ Subgroup.normalizer (R₂ : Set G) :=
    hVS.trans ((show S ≤ Y₂ ⊔ S from le_sup_right).trans
      ((show Y₂ ⊔ S ≤ Y₂ ⊔ S ⊔ Subgroup.zpowers t from le_sup_left).trans hNR₂))
  have hFX : ∀ x ∈ X, ∀ f ∈ V, f * x * f⁻¹ * x⁻¹ ∈ R₂ :=
    commutator_mem_of_mem_sup_centralizer hRlt hR₁R₂ hNV (X := X) (A := V) rfl
  have hRV : R ⊓ V = ⊥ := by rw [inf_comm]; exact V_inf_R h
  have hrel : R.relIndex V = 4 := by
    have hrels := Subgroup.relIndex_mul_card (H := R) (K := V)
    rw [hRV, Subgroup.card_bot, mul_one] at hrels
    exact hrels.trans (card_V h).2
  have h4Xlt : 4 * Nat.card X < Nat.card R₁ := by
    have hlt := hFF V X hVS hVQ hX₂ hX₁ hFX
    rwa [hrel] at hlt
  have hle := card_le_four_mul_card h (R := R) (R₁ := R₁) (R₂ := R₂) (V := V) (X := X)
    rfl hR₁R rfl hRlt hX₁ rfl
  exact absurd h4Xlt (not_lt.mpr hle)

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16

end
