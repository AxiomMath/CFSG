module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public meta import Certificates.Data.A5
import CFSG.GH74.GLS.C3.Layer2.L5C0
import CFSG.GH74.GLS.C3.Layer2.L5B7
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.PSL2Table.BlocksProduct
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.Foundations
import CFSG.GH74.GLS.C3.Layer2.L5B3
import CFSG.GH74.GLS.C3.Layer2.L5B4
import CFSG.GH74.GLS.C3.Layer2.L5B5
import CFSG.GH74.GLS.C3.Layer2.L5Pat
import CFSG.GH74.GLS.C3.Layer3.Main
import CFSG.GH74.GLS.C3.Layers
import CFSG.GH74.GLS.C3.Prop121.Defs
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5070

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

private theorem el16_zero_0 : el16 0 = 1 := by
  decide +kernel

end CertificateChecks.Batch5070

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5070 : el16 0 = 1 := by
  exact CertificateChecks.Batch5070.el16_zero_0

end Certificates
