module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLin
import CFSG.LocalAnalysis.StandardType.GGFFModelSL
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.Adapters.StatedSLTwoField
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.FF81

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped MatrixGroups

theorem exists_model_of_statedClassicalModel {L : Type} [Group L] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (h : StatedClassicalModel L .PSL (n + 1) 2 1) : ∃ z : Fin 3 → L, GGFF.Model L z := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl h
  rcases hn with rfl | rfl
  · exact ⟨_, GGFF.model_SL6.ofMulEquiv e.symm⟩
  · exact ⟨_, GGFF.model_SL7.ofMulEquiv e.symm⟩

private theorem center_eq_bot_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnonab
    have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem ff81bThmAAtFiveSixLab_of_pieces
    (hCurtis : CurtisA2) (hLoc : LocalSetup) (h1 : PropOne) (h2 : PropTwo)
    (hFrame : FrameStep) (hY : ConstructY) (hA : CentralizerA) (hE : CentralizerE6)
    (hFus : RootFusionE6) (hHolt : HoltEnd) :
    FF81bThmAAtFiveSixLab := by
  intro G _ _ _ hnonab hchar hKP n hn b hb L hLC hCN hLmod hcyc hrank hwc
  have hA1 : HypA G n b L := ⟨hn, hb, hLC, hCN, hLmod, hcyc, hrank, hwc⟩
  obtain ⟨z, hz⟩ := exists_model_of_statedClassicalModel hn hLmod
  have hloc : LocalFacts b L z := hLoc G hnonab hchar n b L hA1 z hz
  have hmeet : ∃ g : G, g * b * g⁻¹ ∈ L := h1 G hnonab hchar hKP n b L hA1 z hz hloc
  have hout : PropTwoOut b L z := h2 G hnonab hchar n b L hA1 z hz hloc hmeet
  have hafter : AfterProp2 b L z := ⟨hz, hloc, hmeet, hout⟩
  obtain ⟨K, t, hK⟩ := hFrame G hnonab hchar n b L hA1 z hafter
  have hup : Upstream n b L K t := ⟨z, hafter, hK⟩
  have hYd := hY hCurtis G hnonab hchar n b L hA1 K t hup
  have hcent : Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    rcases hYd.lab with hlab | ⟨h5, hlab⟩
    · exact hA G hnonab hchar n b L hA1 K t hup hYd hlab
    · exact hE G hnonab hchar n b L hA1 K t hup hYd h5 hlab
  have hconj : ∀ g : G, g * t * g⁻¹ ∈ (⨆ i : Fin (n + 2), K (i : ℕ)) →
      ∃ y ∈ (⨆ i : Fin (n + 2), K (i : ℕ)), g * t * g⁻¹ = y * t * y⁻¹ := by
    rcases hYd.lab with hlab | ⟨h5, hlab⟩
    · obtain ⟨S, hS, htS, ht2, hcS⟩ := hYd.syl
      exact rootFusionLin _ (n + 3) (by omega) hlab S hS t htS ht2 hcS hcent
    · exact hFus G hnonab hchar n b L hA1 K t hup hYd h5 hlab hcent
  generalize (⨆ i : Fin (n + 2), K (i : ℕ)) = Y at hYd hcent hconj
  obtain ⟨S, hS, htS, ht2, hcS⟩ := hYd.syl
  have hfus : ∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y := by
    intro g hg
    obtain ⟨y, hy, hgy⟩ := hconj g hg
    have hyg : y⁻¹ * g ∈ Subgroup.centralizer ({t} : Set G) := by
      have hcomm : (y⁻¹ * g) * t * (y⁻¹ * g)⁻¹ = t :=
        calc (y⁻¹ * g) * t * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * t * g⁻¹) * y := by group
          _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [hgy]
          _ = t := by group
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y⁻¹ * g * t = ((y⁻¹ * g) * t * (y⁻¹ * g)⁻¹) * (y⁻¹ * g) := by group
        _ = t * (y⁻¹ * g) := by rw [hcomm]
    have hmem : y⁻¹ * g ∈ Y := hcent hyg
    have hgeq : g = y * (y⁻¹ * g) := by group
    rw [hgeq]
    exact Y.mul_mem hy hmem
  have htop : Y = ⊤ := by
    by_contra hne
    exact hHolt G inferInstance hchar n hn Y S t hYd.lab hne hS htS ht2 hcS hfus
  subst htop
  rcases hYd.lab with hlab | ⟨h5, hlab⟩
  · exact Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hlab)
  · refine Or.inr ⟨h5, ?_⟩
    have hcen : Subgroup.center G = ⊥ := center_eq_bot_of_simple hnonab
    exact ggHasLabel_of_mulEquiv
      (Subgroup.topEquiv.trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcen).symm)) hlab

end CFSG.StandardType.FF81

end
