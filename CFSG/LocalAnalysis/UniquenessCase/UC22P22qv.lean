module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22q
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qd
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC6Pgrp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxL2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThreeCoreUniqueness.Helpers (gamma_le_iff gamma_normalizer_le)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_normalizer_le (D : Data G) (hstd : Sigma23Std D) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup G} (hP : IsSylowOf p P D.M) : normalizer (P : Set G) ≤ D.M := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have h2 : 2 ≤ CFSG.Open.pRank p P := (D.sig_rank p hp).trans (uc22p22q_pRank_le_sylow hP)
  exact (gamma_normalizer_le 2 p P P le_rfl h2).trans (hstd.gamma_two p hp P hP)

theorem uc22p22q_weak_elem {P P₀ : Subgroup G} (hwc : IsWeaklyClosedIn P₀ P) :
    ∀ g : G, (∀ x ∈ P₀, g⁻¹ * x * g ∈ P) → ∀ x ∈ P₀, g⁻¹ * x * g ∈ P₀ := by
  intro g hg x hx
  have hle : CFSG.conjugate P₀ g ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hg y hy
  have h := hwc g hle
  have hxm : g⁻¹ * x * g ∈ CFSG.conjugate P₀ g := ⟨x, hx, by simp⟩
  rwa [h] at hxm

theorem uc22p22q_mem_normalizer_centralizer {P₀ : Subgroup G} {n : G}
    (hn : n ∈ normalizer (P₀ : Set G)) : n ∈ normalizer ((centralizer (P₀ : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ normalizer (P₀ : Set G), ∀ c ∈ centralizer (P₀ : Set G),
      m * c * m⁻¹ ∈ centralizer (P₀ : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro z hz
    have hz' : m⁻¹ * z * m ∈ P₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hm) z).1 hz
      simpa using this
    have h1 := hc _ hz'
    calc z * (m * c * m⁻¹) = m * ((m⁻¹ * z * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * z * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * z := by group
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact key n hn c
  · intro hc
    have := key n⁻¹ (inv_mem hn) _ hc
    simpa [mul_assoc] using this

theorem uc22p22q_stronglyClosed_P1 (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hwc : IsWeaklyClosedIn P₀ P)
    (hcent : P ≤ centralizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)) :
    CFSG.IsStronglyClosedIn P ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  haveI : Fact p.Prime := ⟨(D.sig_prime p hpσ).1⟩
  have hPG : IsSylowOf p P ⊤ := uc22p22q_isSylowOf_top D hstd hpσ hH.sylow
  have hwe := uc22p22q_weak_elem hwc
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed (D.sig_prime p hpσ).1 hH.sylow.isPGroup hH.le hH.card hwe
  have hcen₁ : ∀ y ∈ P, ∀ a ∈ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)), y * a = a * y :=
    fun y hy a ha => ((Subgroup.mem_centralizer_iff.1 (hcent hy)) a ha).symm
  refine ⟨fun a ha => ha.1, ?_⟩
  refine uc22p22q_stronglyClosed_lift hPG hH.le hcen₀ hwe hcen₁ ?_
  intro a ha n hn hnP
  refine ⟨hnP, ?_⟩
  have h1 := uc22p22q_inftyOf_conj (uc22p22q_mem_normalizer_centralizer (inv_mem hn)) ha.2
  simpa using h1

theorem uc22p22q_inU_of_stronglyClosed (D : Data G) (hstd : Sigma23Std D) {p : ℕ} (hp : p ∈ D.sig)
    {P P₁ : Subgroup G} (hP : IsSylowOf p P D.M) (hP₁P : P₁ ≤ P)
    (hcen : ∀ y ∈ P, ∀ a ∈ P₁, y * a = a * y)
    (hsc : ∀ a ∈ P₁, ∀ g : G, g⁻¹ * a * g ∈ P → g⁻¹ * a * g ∈ P₁)
    (hΓ : rankThreeGamma 1 p P₁ ≤ D.M) {X : Subgroup G} (hXP₁ : X ≤ P₁) (hX : X ≠ ⊥) :
    UC6.InU D.M X := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hM : normalizer (D.M : Set G) = D.M := UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hPG : IsSylowOf p P ⊤ := uc22p22q_isSylowOf_top D hstd hp hP
  have hNP : normalizer (P : Set G) ≤ D.M := uc22p22q_normalizer_le D hstd hp hP
  have hXP : X ≤ P := hXP₁.trans hP₁P
  have hXp : IsPGroup p X := hP.isPGroup.to_le hXP
  refine UC6.inU_of_normalizer_le_of_fusion hM (hXP.trans hP.le) ?_ ?_
  · exact (gamma_le_iff 1 p P₁ D.M).1 hΓ X hXP₁
      (UC6.one_le_pRank_of_ne_bot (D.sig_prime p hp).1 hXp hX)
  · intro g hg
    have hmem : ∀ x ∈ X, g⁻¹ * x * g ∈ uniqueFourConj g X := fun x hx => by
      rw [UC6.mem_uniqueFourConj_iff]
      simpa [mul_assoc] using hx
    obtain ⟨k, hkM, hk⟩ := UC6.exists_conj_le_of_isSylowOf hP hg (UC6.isPGroup_uniqueFourConj hXp g)
    have hgkP : ∀ x ∈ X, (g * k)⁻¹ * x * (g * k) ∈ P₁ := by
      intro x hx
      have h1 := hk (g⁻¹ * x * g) (hmem x hx)
      have h2 : (g * k)⁻¹ * x * (g * k) ∈ P := by simpa [mul_assoc] using h1
      exact hsc x (hXP₁ hx) (g * k) h2
    obtain ⟨n, hn, hnx⟩ := uc22p22q_fusion_of_central hPG hXP₁ hcen hgkP
    refine ⟨n * k⁻¹, D.M.mul_mem (hNP hn) (D.M.inv_mem hkM), ?_⟩
    have key : ∀ x ∈ X, g⁻¹ * x * g = (n * k⁻¹)⁻¹ * x * (n * k⁻¹) := by
      intro x hx
      calc g⁻¹ * x * g = k * ((g * k)⁻¹ * x * (g * k)) * k⁻¹ := by group
        _ = k * (n⁻¹ * x * n) * k⁻¹ := by rw [hnx x hx]
        _ = (n * k⁻¹)⁻¹ * x * (n * k⁻¹) := by group
    ext y
    simp only [uniqueFourConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (key x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, key x hx⟩

theorem uc22p22q_P1_ne_bot (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hwc : IsWeaklyClosedIn P₀ P)
    (hL : ∃ n : ℕ, 1 < n ∧ LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n)
    (hp2 : p ≠ 2) : P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) ≠ ⊥ := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hPG : IsSylowOf p P ⊤ := uc22p22q_isSylowOf_top D hstd hpσ hH.sylow
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hpP hH.sylow.isPGroup hH.le hH.card (uc22p22q_weak_elem hwc)
  obtain ⟨n, hn1, hmodel⟩ := hL
  set K : Subgroup G := centralizer (P₀ : Set G) with hK
  set L : Subgroup G := UC6.inftyOf K with hLdef
  have hPK : P ≤ K := fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => (hcen₀ y hy z hz).symm
  have hLK : L ≤ K := Subgroup.map_subtype_le _
  have hKL : K ≤ normalizer (L : Set G) := by
    intro c hc
    have hcn : c ∈ normalizer (K : Set G) := Subgroup.le_normalizer hc
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => uc22p22q_inftyOf_conj hcn hx
    · intro hx
      have := uc22p22q_inftyOf_conj (inv_mem hcn) hx
      simpa [mul_assoc] using this
  have hS : IsSylowOf p (P ⊓ L) L := (hPG.of_le hPK le_top).inf_of_le_normalizer hLK hKL
  intro hbot
  have hcard := hS.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hodd : Odd (p ^ n) := (hpP.odd_of_ne_two hp2).pow
  have hLcard : Nat.card L = p ^ n * (((p ^ n) ^ 2 - 1) / 2) := by
    rw [CFSG.ComponentClassification.CatFactsL4U4.Idx.card_of_lieModel_psl2 hp2 hmodel]
    exact Nat.mul_div_assoc _ ((Nat.Odd.sub_odd (hodd.pow) odd_one).two_dvd)
  have hdvd : p ∣ Nat.card L := by
    rw [hLcard]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  have hpos : 0 < Nat.card L := Nat.card_pos
  have hfac : (Nat.card L).factorization p = 0 := by
    have h1 : p ^ (Nat.card L).factorization p = 1 := hcard.symm
    exact (Nat.pow_eq_one.1 h1).resolve_left hpP.one_lt.ne'
  have h2 := (hpP.dvd_iff_one_le_factorization hpos.ne').1 hdvd
  omega

theorem uc22p22qv_ne_bot_of_pRank {p : ℕ} (hp : p.Prime) {P : Subgroup G} (h : 1 ≤ CFSG.Open.pRank p P) :
    P ≠ ⊥ := by
  rintro rfl
  have : CFSG.Open.pRank p (⊥ : Subgroup G) ≤ 0 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => ?_
    rw [le_bot_iff.1 hE, Subgroup.card_bot]
    simp
  omega

theorem uc22p22q_centralInU_of (D : Data G) (hstd : Sigma23Std D) (hstd2 : Sigma2Std D)
    (h611 : UC6.R6_11Used D) (h613 : UC6.R613Def D) : CentralInU D := by
  intro p hp
  rcases hp with hp2 | hp3
  ·
    have hpσ : p ∈ D.sig := by
      rw [D.sig_sub]
      exact Or.inl (Or.inr hp2)
    haveI : Fact p.Prime := ⟨(D.sig_prime p hpσ).1⟩
    obtain ⟨P, P₀, hH⟩ := hstd2.exists_hyp612 p hp2
    obtain ⟨⟨hp3, -, hwc, hΓ, hL, -⟩, hcent⟩ := h613 p P P₀ hH
    have hsc := (uc22p22q_stronglyClosed_P1 D hstd hH hwc hcent).2
    have hne := uc22p22q_P1_ne_bot D hstd hH hwc hL (by omega)
    have hcen : ∀ y ∈ P, ∀ a ∈ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)), y * a = a * y :=
      fun y hy a ha => ((Subgroup.mem_centralizer_iff.1 (hcent hy)) a ha).symm
    refine ⟨P, hH.sylow, uc22p22q_isSylowOf_top D hstd hpσ hH.sylow, P ⊓ UC6.inftyOf
      (centralizer (P₀ : Set G)), inf_le_left, fun x hx y hy => (hcen y hy x hx).symm, ?_⟩
    exact uc22p22q_inU_of_stronglyClosed D hstd hpσ hH.sylow inf_le_left hcen hsc hΓ le_rfl hne
  ·
    have hp3' : p = 3 := hstd.sig3_sub hp3
    subst hp3'
    have hpσ : 3 ∈ D.sig := by
      rw [D.sig_sub]
      exact Or.inr hp3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := exists_isSylowOf 3 D.M
    obtain ⟨-, -, h3, -, -⟩ := h611 hp3 P hP
    have hPne : P ≠ ⊥ := uc22p22qv_ne_bot_of_pRank Nat.prime_three
      (by have := (D.sig_rank 3 hpσ).trans (uc22p22q_pRank_le_sylow hP); omega)
    haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
    haveI : Nontrivial ↥(Subgroup.center ↥P) := hP.isPGroup.center_nontrivial
    have hXne : (Subgroup.center ↥P).map P.subtype ≠ ⊥ := by
      intro h
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
      have hz' : (z : P).1 ∈ (Subgroup.center ↥P).map P.subtype := ⟨z, z.2, rfl⟩
      rw [h, Subgroup.mem_bot] at hz'
      exact hz (Subtype.ext (Subtype.ext hz'))
    refine ⟨P, hP, uc22p22q_isSylowOf_top D hstd hpσ hP, (Subgroup.center ↥P).map P.subtype,
      by rintro _ ⟨x, -, rfl⟩; exact x.2, ?_, h3 _ (UC6.uc22p22q_center_le_thompson P) hXne⟩
    rintro _ ⟨x, hx, rfl⟩ y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨y, hy⟩).symm

theorem uc22p22q_r6_38_23_of (D : Data G) (hstd : Sigma23Std D) (hstd2 : Sigma2Std D)
    (h611 : UC6.R6_11Used D) (h613 : UC6.R613Def D) : UC6.R6_38Sigma23 D :=
  uc22p22q_r6_38_23_of_central D (uc22p22q_centralInU_of D hstd hstd2 h611 h613)

theorem uc22p22q_r6_13_of (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R613Def D) (h4 : UC6.R613Aut D)
    (h5 : UC6.R613Irr D) : UC6.R6_13 D := by
  refine UC6.r6_13_of_parts D (fun p P P₀ hH => ?_) h4 h5
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  obtain ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, hcent⟩ := h613 p P P₀ hH
  have hsc := uc22p22q_stronglyClosed_P1 D hstd hH hwc hcent
  have hcen : ∀ y ∈ P, ∀ a ∈ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)), y * a = a * y :=
    fun y hy a ha => ((Subgroup.mem_centralizer_iff.1 (hcent hy)) a ha).symm
  exact ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, hsc, fun X hX hne =>
    uc22p22q_inU_of_stronglyClosed D hstd hpσ hH.sylow inf_le_left hcen hsc.2 hΓ hX hne⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
