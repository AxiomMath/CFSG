
module

public import CFSG.Quasithin.Background.C1GNC128

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C1GN

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def C129A7Statement : Prop :=
  ∀ X T M L : Subgroup G, CharTwo X → IsSQTKTC X → IsSylowTwoOf T X → cgsIn X T ≤ M → M ≤ X →
    IsBlock2 X L → IsAltType L 7 → ⁅L, thompsonJ T⁆ = L → ¬ L ≤ M → False

@[expose] def C129BorelStatement : Prop :=
  ∀ X T M L : Subgroup G, CharTwo X → IsSQTKTC X → IsSylowTwoOf T X → cgsIn X T ≤ M → M ≤ X →
    IsChi0Block X L → ⁅L, thompsonJ T⁆ = L → ¬ L ≤ M → IsBorelOfBlock L (L ⊓ M)

end Statements

section Theorem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_cgsIn_of_isGNChoice {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤
      cgsIn X T := by
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T hT hT0
  have h1T : C₁ T ≤ T := h1Z.trans (omegaOneCenterOf_le_self T)
  have h2T : C₂ T ≤ T := h2B.trans (baum_le T)
  have h2charT : ((C₂ T).subgroupOf T).Characteristic :=
    characteristic_subgroupOf_trans (baum_le T) h2B (characteristic_baum T) h2char
  refine sup_le ?_ ?_
  · refine le_trans (inf_le_inf_left X (Subgroup.centralizer_le_normalizer _)) ?_
    exact le_iSup_of_le (C₁ T) (le_iSup_of_le h1T (le_iSup_of_le h1ne
      (le_iSup_of_le h1char le_rfl)))
  · exact le_iSup_of_le (C₂ T) (le_iSup_of_le h2T (le_iSup_of_le h2ne
      (le_iSup_of_le h2charT le_rfl)))

theorem isChi0Block_of_isChiBlock (hA7 : C129A7Statement (G := G)) {X T M L : Subgroup G}
    (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M)
    (hMX : M ≤ X) (hL : IsChiBlock X L) (hLJ : ⁅L, thompsonJ T⁆ = L) (hLM : ¬ L ≤ M) :
    IsChi0Block X L := by
  obtain ⟨hblock, htype⟩ := hL
  refine ⟨hblock, ?_⟩
  rcases htype with h | ⟨m, hm, hm3, hAlt⟩
  · exact Or.inl h
  · obtain ⟨k, rfl⟩ := hm
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
    rcases hcases with rfl | rfl | rfl | hk
    · exact Or.inr (Or.inl hAlt)
    · exact Or.inr (Or.inr hAlt)
    · exact (hA7 X T M L hX hSQ hT hcgs hMX hblock hAlt hLJ hLM).elim
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 : 3 ≤ CFSG.Open.pRank 3 L := three_le_pRank_of_isAltType (by omega) hAlt
      have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X :=
        CFSG.SectionRank.pRank_mono (by norm_num) hblock.2.1
      have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 := hSQ.2 3 Nat.prime_three (by norm_num)
      have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
        pRank_top_subtype (p := 3) X
      omega

theorem lemma_C129_of_cgs {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (h126 : C126Statement C₁ C₂) (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h19 : DistinctBlocksCommuteStatement (G := G))
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hcgs : cgsIn X T ≤ M) (hMX : M ≤ X) :
    X = M ∨ ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
      (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧ X = M ⊔ ⨆ i, L i := by
  by_cases hT0 : T = ⊥
  ·
    left
    refine le_antisymm ?_ hMX
    have hO : pCoreOf 2 X ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
    rw [hT0, le_bot_iff] at hO
    intro x hx
    have : x ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨hx, ?_⟩
      rw [hO]
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [show h = 1 from by simpa using hh]; simp
    have h2 := hX this
    rw [hO] at h2
    have hx1 : x = 1 := by simpa using h2
    rw [hx1]
    exact M.one_mem
  · exact lemma_C128_of_le hC h126 h127 h123 h19 h116 hB42 hX hSQ h38 hT hT0
      ((le_cgsIn_of_isGNChoice hC hT.2.1 hT0).trans hcgs) hMX

theorem lemma_C129 {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (h126 : C126Statement C₁ C₂) (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h19 : DistinctBlocksCommuteStatement (G := G))
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    (hA7 : C129A7Statement (G := G)) (hborel : C129BorelStatement (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hcgs : cgsIn X T ≤ M) (hMX : M ≤ X) :
    ∃ (r : ℕ) (L : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChi0Block X (L i) ∧ IsBorelOfBlock (L i) (L i ⊓ M) ∧
        ⁅L i, thompsonJ T⁆ = L i) ∧ X = M ⊔ ⨆ i, L i := by
  rcases lemma_C129_of_cgs hC h126 h127 h123 h19 h116 hB42 hX hSQ h38 hT hcgs hMX with
    h | ⟨s, L, -, hs2, hL, hXL⟩
  · refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, ?_⟩
    simpa using h
  · refine ⟨s, L, hs2, fun i => ?_, hXL⟩
    obtain ⟨hLchi, hLJ, hLM⟩ := hL i
    have hL0 : IsChi0Block X (L i) :=
      isChi0Block_of_isChiBlock hA7 hX hSQ hT hcgs hMX hLchi hLJ hLM
    exact ⟨hL0, hborel X T M (L i) hX hSQ hT hcgs hMX hL0 hLJ hLM, hLJ⟩

end Theorem

end C1GN

end CFSG.Quasithin
