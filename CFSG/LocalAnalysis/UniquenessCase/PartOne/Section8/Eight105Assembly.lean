module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Radical
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Action
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Thompson
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Fixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

variable {G : Type} [Group G] [Finite G]

private theorem exists_cex8105 {D : Data G} {L P B H N₀ : Subgroup G}
    (hH : H ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B))
    (ih : ∀ H' ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B),
      H < H' → UniqueMax D.M H')
    (hN₀ : N₀ ∈ calMOf H) (hN₀ne : N₀ ≠ D.M) :
    ∃ N : Subgroup G, Cex8105 D L P B H N := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let t : Set (Subgroup G) := {N' | N' ∈ calMOf H ∧ N' ≠ D.M}
  obtain ⟨N, hNt, hNmax⟩ := Set.exists_max_image t
    (fun N' => (Nat.card (D.M ⊓ N' : Subgroup G)).factorization 2)
    (Set.toFinite t) ⟨N₀, hN₀, hN₀ne⟩
  exact ⟨N, ⟨hH, ih, hNt.1, hNt.2, fun N' hN' hne => hNmax N' ⟨hN', hne⟩⟩⟩

private theorem false_of_ctx8105 (hRad : KU45Radical) (hBO : KU45BorelOrders)
    (hF5 : KU45AutOdd) (hS : KSuzukiL2) (hU3 : KU3Ident) (hM3 : KU3Mult) (hF : KU3Facts)
    (h332 : UCK.K332ThreeAb) {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : False := by
  by_cases hC : UC6.calCGS (pCoreOf 2 H) ≤ D.M
  · obtain ⟨hsimp, g, hg, hgo, hidx, hinv⟩ := action_facts hU3 hM3 hF h332 hS c hC
    exact false_of_action c hC hsimp hg hgo hidx hinv
  · have hmax : ∀ H' ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B),
        ¬ H < H' := by
      intro H' hH' hlt
      exact hC (calCGS_le_of_lt_mem c.toCex8105 hH' hlt)
    have hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' →
        H ≤ normalizer (R' : Set G) → pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H := by
      intro R' hR'M hR'2 hHR' hle
      exact eq_pCoreOf_of_maximal c.toCex8105.memH hmax hR'M hR'2 hHR' hle
    obtain ⟨T₁, hT₁, hT₁R⟩ :=
      exists_sylow_le_normalizer hRad hBO hF5 c.toStd8105 c.toCex8105.memH hR
    obtain ⟨T, hT, hTle⟩ := exists_sylow_le_inf c.toCex8105 hC hT₁ hT₁R
    exact false_of_sylow hU3 hF h332 hS c
      (CFSG.ABGLocalTools.IsSylowOf.of_le hT (le_trans hTle inf_le_right) le_top)
      (le_trans hTle inf_le_left)

theorem r8_105_at_of_inputs (hK1 : KU45Lines) (hCP : KU45CentP) (hGR : KU45GenRank)
    (hF5 : KU45AutOdd) (hRad : KU45Radical) (hBO : KU45BorelOrders) (hS : KSuzukiL2)
    (hU3 : KU3Ident) (hM3 : KU3Mult) (hF : KU3Facts) (hK2 : KU45Syl3)
    (h332 : UCK.K332ThreeAb) {D : Data G} (hSg : SigmaStd D) (h61 : UC6.R6_1 D)
    {L P : Subgroup G} {p n : ℕ} (hHyp : F08.Hyp8102 D L P p n)
    (h8103 : R8103At D L P p n) : R8105At D L P n := by
  intro B hB
  have s : Std8105 D L P B p n := std8105_of_at hK2 hSg h61 hHyp hB h8103
  obtain ⟨B', D₀, hl⟩ := exists_lines8105 hK1 hCP hGR s
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  haveI : WellFoundedGT (Subgroup G) := Finite.to_wellFoundedGT
  intro H
  induction H using WellFoundedGT.induction with
  | _ H ih =>
    intro hHmem
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hHmem.1⟩, ?_⟩
    intro N hN
    by_contra hNne
    obtain ⟨N', cx⟩ := exists_cex8105 hHmem (fun H' hH' hlt => ih H' hlt hH') hN hNne
    exact (false_of_ctx8105 hRad hBO hF5 hS hU3 hM3 hF h332
      { toStd8105 := s, toLines8105 := hl, toCex8105 := cx }).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
