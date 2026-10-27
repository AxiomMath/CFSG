module

public import CFSG.LocalAnalysis.StandardType.GGFFSLSylow
public import CFSG.LocalAnalysis.StandardType.GGFFSLClasses
public import CFSG.LocalAnalysis.StandardType.GGFFSLFive
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Statements

@[expose] public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

theorem model_SL6 : Model SL(6, ZMod 2) W6.T where
  simple := isSimpleGroup_SL_zmod_two (by norm_num)
  pow_z := W6.pow_T
  comm_z := W6.comm_T
  inj := W6.inj_T
  inner_odd := inner_odd_SL (by norm_num)
  rank := rank_SL6
  torus := torus_SL6
  fus := fus_SL6
  conj_iff := conj_iff_SL6
  mono := mono_SL6
  no_five := no_five_SL6
  five := five_SL6

theorem model_SL7 : Model SL(7, ZMod 2) W7.T where
  simple := isSimpleGroup_SL_zmod_two (by norm_num)
  pow_z := W7.pow_T
  comm_z := W7.comm_T
  inj := W7.inj_T
  inner_odd := inner_odd_SL (by norm_num)
  rank := rank_SL7
  torus := torus_SL7
  fus := fus_SL7
  conj_iff := conj_iff_SL7
  mono := mono_SL7
  no_five := no_five_SL7
  five := five_SL7

end CFSG.StandardType.GGFF

end
