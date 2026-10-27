
module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMainBase
public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Blueprint.Catalog
import Certificates.Kernel.Misc.Tits.Chain8071
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

namespace CertificateChecks.Batch8071

private theorem sOK : allN 2 (fun j => Nat.beq (TitsCh.S j) (TitsD.S j)) = true := by quickRfl

private theorem sEq {j : Nat} (hj : j < 2) : TitsCh.S j = TitsD.S j :=
  Nat.eq_of_beq_eq_true (allN_spec sOK j hj)

private theorem textLines_nl (cs : List Char) :
    CFSG.YGroups.ModelNative.textLines (String.ofList ('\n' :: cs)) =
      CFSG.YGroups.ModelNative.textLines (String.ofList cs) := by
  rw [CFSG.KS.DecLines.textLines_ofList, CFSG.KS.DecLines.textLines_ofList,
    List.splitOnP_cons_eq_ite_modifyHead]
  simp

private theorem words_eq : titsWords = TitsCT.words.toArray := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsCT.ok).2
  rw [← CFSG.KC.YModel.charsOf_eq] at h
  have e : CFSG.YGroups.ModelNative.chainWords titsChainText =
      CFSG.YGroups.ModelNative.chainWords (String.ofList (CFSG.KC.YModel.charsOf TitsCT.CH)) := by
    rw [TitsCT.eq]
    unfold CFSG.YGroups.ModelNative.chainWords
    simp only [List.replicate_one, List.append_eq, List.singleton_append, textLines_nl]
  rw [titsWords, e, h]
  rfl

private theorem strong_eq : titsStrong =
    (CFSG.YGroups.ModelNative.strongOf 1755 titsGens TitsCT.words.toArray).1 := by
  rw [titsStrong, words_eq]

private theorem baseOK : allN 7 (fun t => Nat.beq ((titsBase.map Fin.val).toArray)[t]!
    (pg 11 (mask 11) TitsCh.BP t)) = true := by quickRfl

private theorem perms : allN 14 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsCh.S j)
    (TitsCh.SI j)) = true := by
  quickRfl

private theorem rep2 (A : Array (List Int)) {j : Nat} (hj : j < 2) :
    (Array.replicate 2 ([] : List Int) ++ A)[j]! = [] := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left (by simp; omega)]
  simp

private theorem words_raw : titsRawWords =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 14 TitsCT.words := by
  have hl : TitsCT.words.length = 12 := by
    simp [TitsCT.words, CFSG.KC.TitsChain.linesWK, TitsCT.lines]
  apply wordsArr_eq
  · simp [titsRawWords, words_eq, hl]
  · omega
  · intro j hj
    exact rep2 _ hj
  · simp [titsRawWords, words_eq]

end CertificateChecks.Batch8071

end
