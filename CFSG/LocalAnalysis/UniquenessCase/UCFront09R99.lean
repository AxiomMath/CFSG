module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.Adapters.GeneralizedFitting
import CFSG.CGT.PushingUpLit.A78Sp4.CentAux
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup le_normalizer_pCoreOf
  le_pCoreOf_of_le_normalizer)

variable {G : Type} [Group G] [Finite G]

theorem r99_holds (D : Data G) : R99 D := by
  intro Y hY hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYmax : Maximal (· ∈ calY2_9 D) Y := hY
  have hYM : Y ≤ D.M := hYmax.prop.1.1
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hRY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
  have hRp : IsPGroup 2 (pCoreOf 2 Y) := pCoreOf_isPGroup 2 Y
  have hYnR : Y ≤ normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
  suffices hc : CFSG.QuasithinUnique.CharTwo Y by
    have hF := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).1
      ((CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP (K := Y)).1 hc)
    unfold Fstar pCoreOf
    rw [CFSG.Adapters.genFittingFStar_eq_foundations, hF]
  have key : ∀ V O : Subgroup G, Y ≤ V → O ≤ pCoreOf 2 Y →
      V ⊓ centralizer (O : Set G) ≤ O → CFSG.QuasithinUnique.CharTwo Y :=
    fun V O hYV hOR hVO x hx => hOR (hVO ⟨hYV hx.1, centralizer_le hOR hx.2⟩)
  by_cases hNR : normalizer (pCoreOf 2 Y : Set G) ≤ D.M
  · obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
      by_contra h'
      exact hYmax.prop.2.1 (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hYM⟩,
        fun N hN => Classical.byContradiction fun hNM => h' ⟨N, hN, hNM⟩⟩)
    have hYW : Y ≤ N ⊓ D.M := le_inf hN.2 hYM
    have hSW := (opp_eq_L9_and_isSylowOf D hY hYW inf_le_right ⟨hN.1, inf_le_left⟩ hNM hS).2
    have hYQ : Y ≤ normalizer (pCoreOf 2 N : Set G) := hN.2.trans (le_normalizer_pCoreOf 2 N)
    have hYn : Y ≤ normalizer ((pCoreOf 2 N ⊓ normalizer (pCoreOf 2 Y : Set G) : Subgroup G) : Set G) :=
      (le_inf hYQ (hYnR.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have hNQp : IsPGroup 2 ↥(pCoreOf 2 N ⊓ normalizer (pCoreOf 2 Y : Set G)) :=
      (pCoreOf_isPGroup 2 N).to_le inf_le_left
    have hNQS : pCoreOf 2 N ⊓ normalizer (pCoreOf 2 Y : Set G) ≤ S := by
      have hle : (pCoreOf 2 N ⊓ normalizer (pCoreOf 2 Y : Set G)) ⊔ S ≤ N ⊓ D.M :=
        sup_le (le_inf (inf_le_left.trans (pCoreOf_le 2 N)) (inf_le_right.trans hNR))
          (hS.le.trans hYW)
      rw [← hSW.eq_of_le le_sup_right hle (hNQp.to_sup_of_normal_left' hS.isPGroup
        (hS.le.trans hYn))]
      exact le_sup_left
    have hNQR : pCoreOf 2 N ⊓ normalizer (pCoreOf 2 Y : Set G) ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 (hNQS.trans hS.le) hYn hNQp
    have hQR : pCoreOf 2 N ≤ pCoreOf 2 Y := by
      by_contra hQR
      have hRnQ : pCoreOf 2 Y ≤ normalizer (pCoreOf 2 N : Set G) := hRY.trans hYQ
      have hlt : pCoreOf 2 Y < pCoreOf 2 N ⊔ pCoreOf 2 Y :=
        lt_of_le_of_ne le_sup_right fun h => hQR (h ▸ le_sup_left)
      obtain ⟨x, hxQR, hxR, hxN⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_not_mem_of_lt_of_isPGroup
        ((pCoreOf_isPGroup 2 N).to_sup_of_normal_left' hRp hRnQ) hlt
      have hx' : x ∈ ((pCoreOf 2 N ⊔ pCoreOf 2 Y : Subgroup G) : Set G) := hxQR
      rw [coe_mul_of_right_le_normalizer_left _ _ hRnQ] at hx'
      obtain ⟨q, hq, r, hr, rfl⟩ := hx'
      have hqN : q ∈ normalizer (pCoreOf 2 Y : Set G) := by
        simpa using (normalizer _).mul_mem hxN ((normalizer _).inv_mem (le_normalizer hr))
      exact hxR ((pCoreOf 2 Y).mul_mem (hNQR ⟨hq, hqN⟩) hr)
    exact key N (pCoreOf 2 N) hN.2 hQR (D.standing.charTwo N hN.1.1)
  · have hloc : IsTwoLocal (normalizer (pCoreOf 2 Y : Set G)) := ⟨pCoreOf 2 Y, hR, hRp, rfl⟩
    obtain ⟨N, hRN, hmax⟩ := Finite.exists_le_maximal hloc
    have hYV : Y ≤ D.M ⊓ normalizer (pCoreOf 2 Y : Set G) := le_inf hYM hYnR
    have hSV := (opp_eq_L9_and_isSylowOf D hY hYV inf_le_left
      ⟨⟨hmax.1, fun K hK hNK => le_antisymm (hmax.2 hK hNK) hNK⟩, inf_le_right.trans hRN⟩
      (fun h => hNR (h ▸ hRN)) hS).2
    have hVc := CFSG.QuasithinUnique.CharTwo.inf_normalizer (D.standing.charTwo D.M D.maxLocal.1)
      (hRY.trans hYM) hRp
    have hOR : pCoreOf 2 (D.M ⊓ normalizer (pCoreOf 2 Y : Set G)) ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2
        ((CFSG.CGT.PushingUpLit.A78Sp4.pCoreOf_le_of_isSylowOf hSV).trans hS.le)
        (hYV.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    exact key _ _ hYV hOR hVc

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
