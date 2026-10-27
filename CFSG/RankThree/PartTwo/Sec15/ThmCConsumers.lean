module

public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofComm
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofOff
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem step171CommQ_of_pCoreOf_mem
    (hQ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17.Sec17Std G A c L Y₀ → CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) :
    Sec17.Step171CommQ := by
  intro G _ _ A c L Y₀ h b hbA _ _ B hB _ hcB
  have hV := hQ G A c L Y₀ h
  have hD := h.toSec15R.toSec14Std.toSec13Data
  obtain ⟨-, hAab, -⟩ := Sec14.Proof1418Res3.max_of_sec13 hD
  have hAY : A ≤ Subgroup.normalizer (Y₀ : Set G) := h.mem_y0Star.prop.1.1.2
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hAb : A ≤ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
    fun a ha => Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAab b hbA a ha).symm)
  have hcA : c ∈ A := hD.mem_A
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    fun a ha => Sec14.centralizer_singleton_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAab c hcA a ha).symm)
  set W := CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAV ha, hAb ha⟩
  have hle : ⁅W, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hAV hcA)))
  have hP : ⁅W, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hV hle (Sec17.Proof171Steps.le_normalizer_commutator hAW hAc)
  exact hP.2 B hB

theorem lemma8_of_comm {A : Subgroup G} {Y : Subgroup G} (hA : IsE27 A)
    (h146 : Sec14.Item146 A (lB A)) (h142 : Sec14.Concl142 A (lB A))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : Subgroup.zpowers e ∈ omegaA A)
    (hN : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∈ scriptQ A (lB A))
    (hc : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers e⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
  Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_le hA h146 hAY (zpowers_mem_omegaA_iff.mp he).1 hN hc
    (Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 he
      (Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf Y)
      (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)))

theorem step171CommQ_of_thmC
    (hC : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A)) :
    Sec17.Step171CommQ := by
  apply step171CommQ_of_pCoreOf_mem
  intro G _ _ A c L Y₀ h
  exact hC G A c L h.toSec15R Y₀ (Sec15.scriptY0Star_subset A (lB A) h.mem_y0Star)

end CFSG.RankThree.PartTwo.Sec15.ThmC
