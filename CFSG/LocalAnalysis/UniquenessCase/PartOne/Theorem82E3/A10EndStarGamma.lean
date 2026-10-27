module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctor
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarGammaCore
import CFSG.RankThree.PartOne.S8.ResidualBound
import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit
import CFSG.HardMathSupport.Solomon.Coordinator.B3Local
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Blueprint (LieModel)

@[expose] def KFactE27TwoGen : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (P A : Subgroup L), CFSG.Open.IsKGroup L →
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
    Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) → A ≤ P → CFSG.Open.IsElemAbelian 3 A →
    Nat.card A = 27 →
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1

@[expose] def KFactE27SignalizerExceptional : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ L : Subgroup X, CFSG.IsComponent L → Subgroup.centralizer (L : Set X) = ⊥ → P ≤ L →
    (UC22.IsAlt ↥L 9 ∨ LieModel ↥L .PSp 2 3 1 ∨ LieModel ↥L .PSU 4 2 1 ∨
      LieModel ↥L .PSp 3 2 1) →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W = ⊥

private lemma map_glbCore_le_glbCore_map {G : Type} [Group G] [Finite G]
    {p k : ℕ} (hp : 1 < p) (L : Subgroup G) (A' : Subgroup ↥L) :
    (CFSG.Open.GLBCore p k A').map L.subtype ≤
      CFSG.Open.GLBCore p k (A'.map L.subtype) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q hQA hk
  calc Subgroup.normalizer (Q : Set ↥L)
      ≤ Subgroup.comap L.subtype
          (Subgroup.normalizer ((Q.map L.subtype) : Set G)) :=
        (Subgroup.le_comap_map L.subtype (Subgroup.normalizer (Q : Set ↥L))).trans
          (Subgroup.comap_mono (Subgroup.le_normalizer_map L.subtype))
    _ ≤ Subgroup.comap L.subtype
          (CFSG.Open.GLBCore p k (A'.map L.subtype)) :=
        Subgroup.comap_mono
          (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
            (Subgroup.map_mono hQA)
            (hk.trans (CFSG.SectionRank.pRank_le_map hp L.subtype L.subtype_injective Q)))

private lemma eq_of_isElemAbelian_card27_of_zwr {X : Type} [Group X] [Finite X]
    {P : Subgroup X} (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    {E F : Subgroup X} (hEP : E ≤ P) (hFP : F ≤ P)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hEcard : Nat.card E = 27) (hFcard : Nat.card F = 27) : E = F := by
  obtain ⟨e⟩ := hPZ
  obtain ⟨A, -, -, -, huniq, -⟩ := UC22.InS3.UC326.zwr_unique_E27 (n := 1) le_rfl e
  have hEA : E.subgroupOf P = A := huniq (E.subgroupOf P) (hE.subgroupOf P) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hEcard])
  have hFA : F.subgroupOf P = A := huniq (F.subgroupOf P) (hF.subgroupOf P) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hFcard])
  calc E = (E.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hEP).symm
    _ = (F.subgroupOf P).map P.subtype := by rw [hEA, hFA]
    _ = F := Subgroup.map_subgroupOf_eq_of_le hFP

private lemma normalizer_le_glbCore_of_zwr {X : Type} [Group X] [Finite X]
    {P A : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    Subgroup.normalizer (P : Set X) ≤ CFSG.Open.GLBCore 3 2 A := by
  have hAP : A ≤ P := hX.jA ▸ Subgroup.map_subtype_le _
  have hNPA : Subgroup.normalizer (P : Set X) ≤ Subgroup.normalizer (A : Set X) := by
    intro g hg
    have hPg : P.map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine eq_of_isElemAbelian_card27_of_zwr hPZ ?_ hAP (hX.elem.map _) hX.elem ?_ hX.card
    · exact (Subgroup.map_mono hAP).trans hPg.le
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hX.card]
  have hArank : 3 ≤ CFSG.Open.pRank 3 A := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hX.elem (k := 3) ?_
    rw [hX.card]
    norm_num
  exact hNPA.trans (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := 3) (k := 2) (P := A) (Q := A) le_rfl (by omega))

private lemma le_glbCore_of_isComponent {X : Type} [Group X] [Finite X]
    {P A L : Subgroup X} (hKg : CFSG.Open.IsKGroup X)
    (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (hPL : P ≤ L) (hL : CFSG.IsComponent L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hnotEx : ¬ (UC22.IsAlt ↥L 9 ∨ LieModel ↥L .PSp 2 3 1 ∨
      LieModel ↥L .PSU 4 2 1 ∨ LieModel ↥L .PSp 3 2 1))
    (hTG : KFactE27TwoGen) : L ≤ CFSG.Open.GLBCore 3 2 A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAP : A ≤ P := hX.jA ▸ Subgroup.map_subtype_le _
  have hAL : A ≤ L := hAP.trans hPL
  have hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1 := by
    intro z hz hcomm
    have hzc : z ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun l hl => (hcomm l hl).symm
    rwa [hC, Subgroup.mem_bot] at hzc
  obtain ⟨hLsimple, hLnonab⟩ :=
    CFSG.GH74.Uniqueness.SU.K.R3.component_simple_data hL hZ
  have hKL : CFSG.Open.IsKGroup ↥L := hKg.subgroup L
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P L := hX.sylow.of_le hPL le_top
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    refine le_antisymm (Subgroup.map_subtype_le (H := L) (K := ⊤)) ?_
    intro x hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hPsyl' : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf L) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L]
    rw [Subgroup.map_subgroupOf_eq_of_le hPL, htop]
    exact hPsyl
  have hPZ' : Nonempty (↥(P.subgroupOf L) ≃* UC22.InS3.UC326.ZWr 1) := by
    obtain ⟨e⟩ := hPZ
    exact ⟨(Subgroup.subgroupOfEquivOfLe hPL).trans e⟩
  have hA'P : A.subgroupOf L ≤ P.subgroupOf L := Subgroup.subgroupOf_mono L hAP
  have hA'ea : CFSG.Open.IsElemAbelian 3 (A.subgroupOf L) := hX.elem.subgroupOf L
  have hA'card : Nat.card (A.subgroupOf L) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hX.card]
  have hcore' : CFSG.Open.GLBCore 3 2 (A.subgroupOf L) = ⊤ := by
    rcases hTG ↥L (P.subgroupOf L) (A.subgroupOf L) hKL hLsimple hLnonab hPsyl' hPZ'
      hA'P hA'ea hA'card with h | h
    · exact h
    · exact (hnotEx h).elim
  have hmap := map_glbCore_le_glbCore_map (p := 3) (k := 2) (by norm_num) L
    (A.subgroupOf L)
  have hAmap : (A.subgroupOf L).map L.subtype = A :=
    Subgroup.map_subgroupOf_eq_of_le hAL
  rw [hcore', htop, hAmap] at hmap
  exact hmap

private lemma glbCore_eq_top_of_normalizer {X : Type} [Group X] [Finite X]
    {P A L : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hLn : L.Normal) (hPL : P ≤ L)
    (hLG : L ≤ CFSG.Open.GLBCore 3 2 A) : CFSG.Open.GLBCore 3 2 A = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : L.Normal := hLn
  have hcardP : Nat.card P = 3 ^ (Nat.card X).factorization 3 := by
    rw [hX.sylow.card_eq, Subgroup.card_top]
  let Psyl : Sylow 3 X := Sylow.ofCard P hcardP
  have hcoe : (Psyl : Subgroup X) = P := Sylow.coe_ofCard P hcardP
  have hFrattini : Subgroup.normalizer (P : Set X) ⊔ L = ⊤ := by
    have hPL' : (Psyl : Subgroup X) ≤ L := by rw [hcoe]; exact hPL
    have h := Sylow.normalizer_sup_eq_top' Psyl hPL'
    exact h
  have hNPG := normalizer_le_glbCore_of_zwr hX hPZ
  have htop : (⊤ : Subgroup X) ≤ CFSG.Open.GLBCore 3 2 A := by
    rw [← hFrattini]
    exact sup_le hNPG hLG
  exact top_le_iff.mp htop

theorem kFactE27SignalizerAlmostSimpleSylow_of_twoGen
    (hSF : CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hTG : KFactE27TwoGen) (hEx : KFactE27SignalizerExceptional) :
    KFactE27SignalizerAlmostSimpleSylow := by
  intro X _ _ P A hKg hX hPZ h3' hbal L hL hC hPL W hW hcop
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcat : CFSG.SectionRank.IsKGroupCat X :=
    CFSG.RankThree.PartOne.isKGroupCat_of_isKGroup hbridge
      (CFSG.HardMathSupport.Solomon.Coordinator.isKGroup_of_openIsKGroup hKg)
  by_cases hExc : UC22.IsAlt ↥L 9 ∨ LieModel ↥L .PSp 2 3 1 ∨
      LieModel ↥L .PSU 4 2 1 ∨ LieModel ↥L .PSp 3 2 1
  · exact hEx X P A hKg hX hPZ h3' hbal L hL hC hPL hExc W hW hcop
  · have hLn : L.Normal :=
      CFSG.GH74.Generic.BProg.B3.S1Three.normal_of_centralizer_le hL (z := 1) fun w hw => by
        rw [hC, Subgroup.mem_bot] at hw
        exact Or.inl hw
    have hLG : L ≤ CFSG.Open.GLBCore 3 2 A :=
      le_glbCore_of_isComponent hKg hX hPZ hPL hL hC hExc hTG
    have hgen : CFSG.Open.GLBCore 3 2 A = ⊤ :=
      glbCore_eq_top_of_normalizer hX hPZ hLn hPL hLG
    exact A10Gen.eq_bot_of_glbCore_eq_top hSF Nat.prime_three hX.elem
      (by rw [hX.card]; norm_num) hKcat hbal h3' hgen hW hcop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
