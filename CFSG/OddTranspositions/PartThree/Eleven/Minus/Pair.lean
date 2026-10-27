module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Derived
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Local
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Realize
public import CFSG.OddTranspositions.PSL225OfCard
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.Recognition
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.A7.Glue
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma14j
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.SP.Local.SPLTabL2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem nonempty_minusL_mulEquiv_psl225 : Nonempty (minusL ≃* QZ.PSL225) := by
  have hmem := minusLocal_mem
  have hLP : CFSG.GorensteinWalter.HasDihedralSylowTwo minusLPerm :=
    hasDihedralSylowTwo_of_minusSylow card_minusLPerm hmem.1 hmem.2.1
  have hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo minusL := by
    rw [minusL]
    exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe minusLPerm_le_minusPerm) hLP
  haveI : IsSimpleGroup minusL := isSimpleGroup_minusL
  exact nonempty_mulEquiv_psl225_of_card card_minusL hdih

theorem isO4Minus5Pair_minusPerm : QZ.IsO4Minus5Pair minusPerm minusClass := by
  have hmem := minusLocal_mem
  haveI : minusL.Normal := minusL_normal
  obtain ⟨eL⟩ := nonempty_minusL_mulEquiv_psl225
  have hA5le : minusA5Perm ≤ minusLPerm :=
    minusA5Perm_le hmem.2.2.1 hmem.2.2.2
  have hA5lePerm : minusA5Perm ≤ minusPerm :=
    hA5le.trans minusLPerm_le_minusPerm
  let z : minusPerm := ⟨minusRefl 0, minusRefl_mem 0⟩
  refine QZ.isO4Minus5Pair_of_mulEquiv_psl225 (L := minusL) index_minusL eL
    centralizer_minusL (z := z) ?_ ?_
    (X := minusA5Perm.subgroupOf minusPerm) ?_ ?_ ?_
    (D := minusClass) ⟨_, minusClass_eq_setOf_isConj⟩ ?_ ?_
  · exact Subtype.ext (minusRefl_mul_self 0)
  · exact not_mem_minusL_of_mem_minusClass ⟨0, rfl⟩
  · intro x hx
    exact hA5le hx
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hA5lePerm).trans
      nonempty_minusA5Perm_mulEquiv.some⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact commute_minusRefl_zero_of_mem_minusA5Perm hx
  · intro d hd
    obtain ⟨i, hi⟩ := hd
    apply Subtype.ext
    show (d : Equiv.Perm (Fin 65)) * d = 1
    rw [hi]
    exact minusRefl_mul_self i
  · intro d hd
    exact not_mem_minusL_of_mem_minusClass hd

end CFSG.OddTranspositions.PartThree
