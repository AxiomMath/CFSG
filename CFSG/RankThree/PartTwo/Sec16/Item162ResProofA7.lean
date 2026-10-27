module

import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

namespace Res162

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_normalizer_of_conf162 {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
    (h : Sec15R G A c L) (hconf : Conf162 A (lB A) c L Y₁ Y₂ S)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A))
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (φ₁ : ↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7))
    (hLN : L ≤ Subgroup.normalizer (Y₂ : Set G)) : False := by
  obtain ⟨φL⟩ := h7
  have h14 := h.toSec14Std
  have hY₁ := hconf.maxCE.1.mem₁
  have hY₂ := hconf.maxCE.1.mem₂
  have hcovL : L = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [inf_of_le_right hconf.le_y]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  have hcov₁ : Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁ :=
    eq_sup_of_forall_mem (exists_mem_inf_of_cover hcovL
      (by rw [Nat.card_congr φ₁.toEquiv, Nat.card_congr φL.toEquiv]))
  have hV := Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h14 h1444 h146 hbot h142
    hY₁.prop.1 (Or.inl hcov₁)
  have hOS : CFSG.Open.pCoreOf 2 Y₁ ≤ S :=
    Proof162.pCoreOf_le_of_mem_scriptQ h14.isE27 h146 hconf.maxCE.1.s₁ hV
  have hSN : S ≤ Subgroup.normalizer (Y₂ : Set G) := hconf.maxCE.1.s₂.prop.1.2
  have hY₁N : Y₁ ≤ Subgroup.normalizer (Y₂ : Set G) :=
    hcov₁.le.trans (sup_le (inf_le_right.trans hLN) (hOS.trans hSN))
  obtain ⟨X, hX, hXLY⟩ := hconf.meets₂
  have heq : Y₁ = Y₂ := Proof162.eq_of_le_normalizer_of_mem_scriptY4 hY₁ hY₂.prop hX
    ((hXLY.trans inf_le_left).trans hconf.le_y) (hXLY.trans inf_le_right) hY₁N
  exact hconf.maxCE.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, heq]⟩

end Res162

end CFSG.RankThree.PartTwo.Sec16
