module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThreeCoreUniqueness.Helpers (gamma_le_iff)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_isSylowOf_P1 (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hwc : IsWeaklyClosedIn P₀ P) :
    IsSylowOf p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) (UC6.inftyOf (centralizer (P₀ : Set G))) := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hPG : IsSylowOf p P ⊤ := uc22p22q_isSylowOf_top D hstd hpσ hH.sylow
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hpP hH.sylow.isPGroup hH.le hH.card (uc22p22q_weak_elem hwc)
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
  exact (hPG.of_le hPK le_top).inf_of_le_normalizer hLK hKL

theorem uc22p22q_P1_elem (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hwc : IsWeaklyClosedIn P₀ P)
    (hL : ∃ n : ℕ, 1 < n ∧ LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) (hp2 : p ≠ 2) :
    ∃ n : ℕ, 1 < n ∧ IsElemAbelian p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ∧
      Nat.card (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) = p ^ n := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨n, hn, hmodel⟩ := hL
  set L : Subgroup G := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  have hS : IsSylowOf p (P ⊓ L) L := uc22p22q_isSylowOf_P1 D hstd hH hwc
  have hle : P ⊓ L ≤ L := inf_le_right
  have hS' : IsSylowOf p ((P ⊓ L).subgroupOf L) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) L (A := (P ⊓ L).subgroupOf L) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hS
  obtain ⟨hel, hcard⟩ := uc22p22q_psl2_sylow_elem hpP hp2 hmodel hS'
  refine ⟨n, hn, ?_, ?_⟩
  · exact CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p _ (P ⊓ L)
      (Subgroup.subgroupOfEquivOfLe hle) hel
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcard

theorem uc22p22q_normalizer_P1_le (D : Data G) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hP₁ : P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) ≠ ⊥)
    (hΓ : rankThreeGamma 1 p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ≤ D.M) :
    normalizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) ≤ D.M := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  exact (gamma_le_iff 1 p _ D.M).1 hΓ _ le_rfl
    (UC6.one_le_pRank_of_ne_bot (D.sig_prime p hpσ).1 (hH.sylow.isPGroup.to_inf_left) hP₁)

theorem uc22p22q_irr_P1 (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hwc : IsWeaklyClosedIn P₀ P)
    (hL : ∃ n : ℕ, 1 < n ∧ LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n) (hp2 : p ≠ 2)
    (hΓ : rankThreeGamma 1 p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ≤ D.M) :
    IrrOn (D.M ⊓ normalizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G))
      (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hP₁ := uc22p22q_P1_ne_bot D hstd hH hwc hL hp2
  have hNM := uc22p22q_normalizer_P1_le D hH hP₁ hΓ
  obtain ⟨n, hn, hmodel⟩ := hL
  set L : Subgroup G := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  have hS : IsSylowOf p (P ⊓ L) L := uc22p22q_isSylowOf_P1 D hstd hH hwc
  have hle : P ⊓ L ≤ L := inf_le_right
  have hS' : IsSylowOf p ((P ⊓ L).subgroupOf L) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) L (A := (P ⊓ L).subgroupOf L) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hS
  intro W hWP₁ hWN
  have hWL : W ≤ L := hWP₁.trans hle
  have hW'S : W.subgroupOf L ≤ (P ⊓ L).subgroupOf L := fun x hx => hWP₁ hx
  have hinv : ∀ g : ↥L, g ∈ normalizer (((P ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) →
      (g : G) ∈ normalizer ((P ⊓ L : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhL : h ∈ L := hle hh
      have := (mem_normalizer_iff.1 hg ⟨h, hhL⟩).1 hh
      exact this
    · intro hh
      have hhL : h ∈ L := by
        have h1 : (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem g.2) (hle hh)) g.2
        simpa [mul_assoc] using h1
      exact (mem_normalizer_iff.1 hg ⟨h, hhL⟩).2 hh
  have hW : ∀ g ∈ normalizer (((P ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L), ∀ w ∈ W.subgroupOf L,
      g * w * g⁻¹ ∈ W.subgroupOf L := by
    intro g hg w hw
    have hgN := hinv g hg
    have hgM : (g : G) ∈ D.M := hNM hgN
    have h1 : (g : G) * (w : G) * (g : G)⁻¹ ∈ W :=
      (mem_normalizer_iff.1 (hWN ⟨hgM, hgN⟩) (w : G)).1 hw
    exact h1
  rcases uc22p22q_psl2_borel_irr hpP hp2 hmodel hS' hW'S hW with h | h
  · left
    have := congrArg (fun T : Subgroup ↥L => T.map L.subtype) h
    simp only [Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hWL] at this
    exact this
  · right
    have := congrArg (fun T : Subgroup ↥L => T.map L.subtype) h
    simp only [Subgroup.map_subgroupOf_eq_of_le hWL, Subgroup.map_subgroupOf_eq_of_le hle] at this
    exact this

theorem uc22p22q_r613irr_of (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R613Def D) :
    UC6.R613Irr D := fun p P P₀ hH => by
  obtain ⟨⟨hp3, -, hwc, hΓ, hL, -⟩, -⟩ := h613 p P P₀ hH
  exact uc22p22q_irr_P1 D hstd hH hwc hL (by omega) hΓ

end CFSG.LocalAnalysis.UniquenessCase.UC22
