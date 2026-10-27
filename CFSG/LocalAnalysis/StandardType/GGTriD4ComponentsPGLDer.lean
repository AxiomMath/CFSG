module

public import CFSG.Assembly.GL83LieDefs
import CFSG.Assembly.GL83StatedBridge
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo
open CFSG.PGLModel (projImage)

theorem ggTriD4_pgl_derived_equiv {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) :
    Nonempty (↥⁅projImage (Sec4.glPi true 3 (2 ^ n) F), projImage (Sec4.glPi true 3 (2 ^ n) F)⁆ ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) F)) := by
  have hPi : Sec4.PiField true 2 n F := ⟨Nat.prime_two, by omega, hF⟩
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have h1 : ⁅projImage (Sec4.glPi true 3 (2 ^ n) F), projImage (Sec4.glPi true 3 (2 ^ n) F)⁆ =
      projImage (Sec4.slPi true 3 (2 ^ n) F) := by
    unfold PGLModel.projImage
    rw [← Subgroup.map_commutator, Sec13.commutator_glPi hPi hq2]
  have h2 : Sec4.slPi true 3 (2 ^ n) F = Open.StatedSL 3 F := rfl
  have h3 : LargeEvenSLGroup (Fin 3) F = Open.StatedSL 3 F := largeEvenSLGroup_eq_statedSL 3
  refine ⟨(MulEquiv.subgroupCongr (h1.trans (by rw [h2]))).trans
    ((Census.statedProjEquivProjImage (Open.StatedSL 3 F)).symm.trans ?_)⟩
  rw [h3]

theorem ggTriD4_pgu_derived_equiv {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nonempty (↥⁅projImage (Sec4.glPi false 3 (2 ^ n) F), projImage (Sec4.glPi false 3 (2 ^ n) F)⁆ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ n))) := by
  have hPi : Sec4.PiField false 2 n F := ⟨Nat.prime_two, by omega, hF⟩
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have h1 : ⁅projImage (Sec4.glPi false 3 (2 ^ n) F), projImage (Sec4.glPi false 3 (2 ^ n) F)⁆ =
      projImage (Sec4.slPi false 3 (2 ^ n) F) := by
    unfold PGLModel.projImage
    rw [← Subgroup.map_commutator, Sec13.commutator_glPi hPi hq2]
  have h2 : Sec4.slPi false 3 (2 ^ n) F = Open.StatedSU 3 (2 ^ n) F := rfl
  exact ⟨(MulEquiv.subgroupCongr (h1.trans (by rw [h2]))).trans
    (Census.statedProjEquivProjImage (Open.StatedSU 3 (2 ^ n) F)).symm⟩

theorem ggTriD4_pgu_two_solvable {n : ℕ} (hn : n = 1) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ n) F)) := by
  subst hn
  exact Sec13.isSolvable_projImage_glPi_two ⟨Nat.prime_two, le_rfl, hF⟩ (by norm_num)

end CFSG.StandardType
