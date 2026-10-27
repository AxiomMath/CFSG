module

public import CFSG.RankThree.PartTwo.Sec17.Item17ResProof177
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofMain
public import CFSG.RankThree.PartTwo.Sec17.Item1712ProofRoute

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

theorem step1712Seven_of_B (hmeet : Step177Meet) (hmain : Step177MainB) (h1514 : Item1514S17)
    (h176 : Item176R) (h9 : CardInfNineS17) (hres : Step1712SevenY0) : Step1712Seven := by
  intro G _ _ A c L Y₀ h V hV hVc
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hAM : A ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (h.toSec13Data.commute ha hcA))
  have hAVc : A ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hAV hAc
  have hVcV : ⁅V, Subgroup.zpowers c⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hAV hcA))
  have key : ∀ W : Subgroup G, W ≤ ⁅V, Subgroup.zpowers c⁆ → W ∈ scriptQ A (lB A) → W ≠ ⊥ →
      ∃ U ∈ fourGroups A, U ≤ ⁅V, Subgroup.zpowers c⁆ ∧ U ∈ scriptQ A (lB A) := by
    intro W hWVc hWQ hW1
    obtain ⟨U, hU, hUW, -⟩ := Proof1712.exists_fourGroupsMinus_le_of_le_commutator hA hcA hVab
      hAV hWQ.1.2.2 hWVc hW1
    exact ⟨U, hU.1, hUW.trans hWVc, mem_scriptQ_of_le hWQ hUW hU.1.1.2.2⟩
  have hVYV : ⁅V, Y₀⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.le_normalizer.trans hMV)
  have hVYY : ⁅V, Y₀⁆ ≤ Y₀ := Subgroup.le_normalizer_iff_commutator_le_right.mp hVM
  by_cases hΩ : omegaA A = {Subgroup.zpowers c}
  · by_cases hYV : ⁅Y₀, V⁆ = ⊥
    ·
      have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9 G A c L Y₀ h]⟩
      have hOQ : pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ∈
          scriptQ A (lB A) := Proof17Res.pPrimeCoreOf_centralizer_hyperplane_mem_scriptQ hA hB
      by_cases hU : ⁅V, Subgroup.zpowers c⁆ ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥
      · exact (hmain G A c L Y₀ h (h1514 G A c L Y₀ h) (h176 G A c L h.toSec15R) hΩ V hV hYV
          hVc hU).elim
      · exact key _ inf_le_left (mem_scriptQ_of_le hOQ inf_le_right
          (Late.le_normalizer_inf hAVc hOQ.1.2.2)) hU
    · have hVY : ⁅V, Y₀⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
      obtain ⟨hVYQ, -⟩ := hmeet G A c L Y₀ h V hV hVY
      by_cases hVcY : ⁅V, Subgroup.zpowers c⁆ ⊓ Y₀ = ⊥
      · exact hres G A c L Y₀ h V hV hΩ hVY hVc hVcY
      · exact key _ inf_le_left (mem_scriptQ_of_le hVYQ (inf_le_inf_right _ hVcV)
          (Late.le_normalizer_inf hAVc hAM)) hVcY
  ·
    have hAY : A ≤ Y₀ := h.le_y0_of_alternating_ten (h.a10_or_omega.resolve_right hΩ)
    have hVcY : ⁅V, Subgroup.zpowers c⁆ ≤ ⁅V, Y₀⁆ :=
      Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr (hAY hcA))
    have hVY : ⁅V, Y₀⁆ ≠ ⊥ := fun hb => hVc (le_bot_iff.mp (hb ▸ hVcY))
    obtain ⟨hVYQ, -⟩ := hmeet G A c L Y₀ h V hV hVY
    exact key _ le_rfl (mem_scriptQ_of_le hVYQ (hVcY.trans (le_inf hVYV hVYY)) hAVc) hVc

theorem step1712Seven_of_M (hmeet : Step177Meet) (hM : Step177MainM) (h1514 : Item1514S17)
    (h176 : Item176R) (h9 : CardInfNineS17) (hres : Step1712SevenY0) : Step1712Seven :=
  step1712Seven_of_B hmeet (step177MainB_of_M hM) h1514 h176 h9 hres

theorem item1712S17_of_B
    (h1711 : Item1711S17) (hmeet : Step177Meet)
    (hmain : Step177MainB) (h1514 : Item1514S17) (h176 : Item176R) (hres : Step1712SevenY0)
    (h310 : Sec6.Item3_10) (h9 : CardInfNineS17) (hD : Step1712Delta) : Item1712S17 :=
  item1712S17_of h1711 (step1712Seven_of_B hmeet hmain h1514 h176 h9 hres)
    (step1712Main_of_items h310 h9 hD)

end CFSG.RankThree.PartTwo.Sec17
