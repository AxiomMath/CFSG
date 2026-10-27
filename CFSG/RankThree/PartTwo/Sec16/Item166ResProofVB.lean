module

public import CFSG.RankThree.PartTwo.Sec16.Item167StepsProof
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace ProofVB167

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem lB_eq_bot_of_forall_not_le {B : Subgroup G} (hΩ : ∀ F ∈ omegaA A, ¬ F ≤ B) :
    lB A B = ⊥ :=
  lB_eq_bot fun b d L' hc => by
    obtain ⟨hBbd, hb, -⟩ := hc
    refine hΩ _ hb (Subgroup.zpowers_le.mpr ?_)
    rw [hBbd]
    exact Subgroup.subset_closure (Set.mem_insert b _)

theorem step167VB_of_pCoreOf_mem
    (hQ0 : ∀ Y₀ ∈ scriptY0Star A (lB A), CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) :
    Step167VB A (lB A) c L := by
  intro Y _ _ _ Y₀ hY₀ B hB hΩ
  have h := (hQ0 Y₀ hY₀).2 B hB
  rw [qBound, lB_eq_bot_of_forall_not_le hΩ, sup_bot_eq] at h
  exact (inf_le_inf_right _ inf_le_left).trans h

theorem pCoreOf_mem_scriptQ_of_commutator (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (h142 : Concl142 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    (hN : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A))
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∨ c ∈ Y) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have hA : IsE27 A := h.isE27
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  refine Proof17Q0.pCoreOf_mem_scriptQ_of_scriptY4 hA h146 hY hN hcA ?_
    (Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 h.toSec13Data.zpowers_mem_omegaA
      (Proof17Q0.isPiSubgroup_piCompl_pCoreOf Y) hAV)
  rcases hcov with hcov | hcY
  · exact Or.inr (Proof17Q0.commutatorElement_mem_of_eq_sup hcov
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) (hAV hcA)
      (inf_le_right.trans h.toSec13Data.le_centralizer))
  · exact Or.inl hcY

theorem pCoreOf_mem_scriptQ_of_cover (h : Sec14Std G A c L) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : Concl142 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∨ c ∈ Y) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
  pCoreOf_mem_scriptQ_of_commutator h h146 h142 hY
    (Proof17Q0.commutator_pCoreOf_mem_scriptQ h.isE27 h1444 h146 hbot hY) hcov

theorem cover_of_item163 (h : Sec15R G A c L) (h163 : Item163 A (lB A) c L)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Step163Meets) {Y₀ : Subgroup G}
    (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) :
    Y₀ = (Y₀ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₀ ∨ c ∈ Y₀ := by
  obtain ⟨-, -, -, hLY, h5⟩ := h163 Y₀ hY₀
  rcases h5 with hA10 | hΩ
  · right
    obtain ⟨φ⟩ := hA10
    have hFE : partTwoF G = partTwoE G :=
      (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
    have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
        E ≤ B → B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
    exact Step163Alt.le_of_alternating_ten hmax h.toSec13Data.isElemAbelian hY₀.prop.1.1.2
      hY₀.prop.2.2 φ h.toSec13Data.mem_A
  · left
    have hm : MeetsY4 A (lB A) L Y₀ := hMeets G A c L h Y₀ hY₀ hLY
    rcases h1514 Y₀ hY₀ hm with ⟨hY, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, hY, -⟩
    · exact hY
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
    · exact hY

theorem pCoreOf_mem_scriptQ_of_y0Star (h : Sec15R G A c L) (h163 : Item163 A (lB A) c L)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Step163Meets) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : Concl142 A (lB A)) {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) :
    CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A) :=
  pCoreOf_mem_scriptQ_of_cover h.toSec14Std h1444 h146 hbot h142 hY₀.prop.1
    (cover_of_item163 h h163 h1514 hMeets hY₀)

end ProofVB167

theorem step167VBR_of (h163 : Item163R) (h1514 : Item1514R) (hMeets : Step163Meets)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142R) :
    Step167VBR := fun G _ _ A c L h =>
  ProofVB167.step167VB_of_pCoreOf_mem fun _ hY₀ =>
    ProofVB167.pCoreOf_mem_scriptQ_of_y0Star h (h163 G A c L h) (h1514 G A c L h) hMeets
      (h1444 G A c L h.toSec14Std) (h146 G A c L h.toSec14Std) (hbot G A c L h.toSec14Std)
      (h142 G A c L h) hY₀

theorem step167VR_of_items (h163 : Item163R) (h1514 : Item1514R) (hMeets : Step163Meets)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142R) :
    Step167VR :=
  step167VR_of h142 (step167VBR_of h163 h1514 hMeets h1444 h146 hbot h142)

end CFSG.RankThree.PartTwo.Sec16
