module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Gen
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem genSeven_of_psl2 {Q : Type} [Group Q] [Finite Q]
    {p f : ℕ} (hp3 : p ≠ 3) (hQ : LieModel Q .PSL 2 p f) {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) :
    GenSeven Q X := by
  intro W hXW hD _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hDX, hD3⟩ := exists_le_card_eq_three_of_isL2Odd_seven hX
  obtain ⟨⟨hp, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hQ.statedClassicalModel (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hnc : ¬ IsMulCommutative (Bar2 X) := fun hc => by
    have hpr := (Group.is_simple_iff_prime_card (α := Bar2 X)).mp hsimple
    rw [PartTwo.Inputs1719.card_of_isL2Odd_seven hX] at hpr
    norm_num at hpr
  have hW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := fun hW =>
    false_of_isPSolvable_surj
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hW hXW) ⊤
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.topEquiv (G := ↥X)).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := ↥X)).surjective)
      hsimple hnc (by rw [PartTwo.Inputs1719.card_of_isL2Odd_seven hX]; norm_num)
  have hL2 : OvergroupTransfer.OvergroupEqTop (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    fun hc _ _ hA hNW hW' => OvergroupPSL2.eq_top_of_normalizer_le hF hp3
      (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le E y)
      (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le E y)
      hc hA hNW hW'
  have e : Q ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  exact OvergroupTransfer.overgroupEqTop_of_mulEquiv e hL2 hcyc D W hD3 (hD D hDX hD3) hW

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
