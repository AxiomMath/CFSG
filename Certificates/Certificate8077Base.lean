
module

public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Quasithin.Recognition.CertTitsSimpleMainBase
import CFSG.Blueprint.Catalog
import Certificates.Kernel.Misc.Tits.Prim8077
import Certificates.Kernel.Misc.Tits.Strong8077Base
import Certificates.Kernel.TitsW.Alg
import Certificates.Kernel.Sporadic.Tits.GroupT2264
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import CFSG.Certificates.Kernel.Misc.TitsPrimSound
import CFSG.Certificates.Kernel.Spor.RawOrbSound
import CFSG.Certificates.Kernel.Spor.StrongOfSound
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Spor.PresCardPG
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.YModel.Sound
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.TitsPrim
open CertificateChecks.KernelMisc CertificateChecks.KernelTitsW CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelMisc.TitsPrim8077 CertificateChecks.TitsStrong8077

namespace CertificateChecks.Batch8077

private theorem rep2 (A : Array (List Int)) {j : Nat} (hj : j < 2) :
    (Array.replicate 2 ([] : List Int) ++ A)[j]! = [] := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left (by simp; omega)]
  simp

private theorem words_raw : titsPairRawWords =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 TitsPCT.words := by
  have hl : TitsPCT.words.length = 10 := by
    simp [TitsPCT.words, CFSG.KC.TitsChain.linesWK, TitsPCT.lines]
  apply wordsArr_eq
  · simp [titsPairRawWords, pwords_eq, hl]
  · omega
  · intro j hj
    exact rep2 _ hj
  · simp [titsPairRawWords, pwords_eq]

private theorem labels_eq : titsLabels = CFSG.KC.YModel.unpackA (CFSG.KC.YModel.lget TitsLbT.El 0) 32
    (TitsLbT.F 0) := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsLbT.ok).1
  rw [← CFSG.KC.YModel.charsOf_eq] at h
  have e : titsLabels = CFSG.YGroups.ModelNative.chainBase titsLabelsText := rfl
  rw [e, TitsLbT.eq]
  unfold CFSG.YGroups.ModelNative.chainBase at h ⊢
  simp only [List.replicate_one, List.append_eq, List.singleton_append, textLines_nl]
  exact h

private theorem labels_get {q : Nat} (hq : q < 1755) :
    titsLabels[q]! = CFSG.KC.TitsOuter.labAt (TitsLbT.F 0) q := by
  have hE : CFSG.KC.YModel.lget TitsLbT.El 0 = 1755 := by decide +kernel
  rw [labels_eq, CFSG.KC.YModel.unpackA, getElem!_ofFn_nat _ (by rw [hE]; exact hq)]
  rfl

private theorem roots_eq : titsRoots = CFSG.KC.YModel.unpackA (CFSG.KC.YModel.lget TitsRtT.El 0) 32
    (TitsRtT.F 0) := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsRtT.ok).1
  rw [← CFSG.KC.YModel.charsOf_eq] at h
  have e : titsRoots = CFSG.YGroups.ModelNative.chainBase titsRootsText := rfl
  rw [e, TitsRtT.eq]
  unfold CFSG.YGroups.ModelNative.chainBase at h ⊢
  simp only [List.replicate_one, List.append_eq, List.singleton_append, textLines_nl]
  exact h

private theorem roots_get {i : Nat} (hi : i < 5) :
    titsRoots[i]! = CFSG.KC.YModel.fieldAt 32 (TitsRtT.F 0) i := by
  have hE : CFSG.KC.YModel.lget TitsRtT.El 0 = 5 := by decide +kernel
  rw [roots_eq, CFSG.KC.YModel.unpackA, getElem!_ofFn_nat _ (by rw [hE]; exact hi)]

private theorem tw_eq : titsTw = (((CFSG.KC.LQT.Cov.linesK TitsTwC.chars).drop 1).map fun l =>
    CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray := by
  rw [titsTw, rawLines, TitsTwC.eq, lines_ofList, List.map_map]
  rfl

private theorem hw_eq : titsHw = (((CFSG.KC.LQT.Cov.linesK TitsHwC.chars).drop 1).map fun l =>
    CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray := by
  rw [titsHw, rawLines, TitsHwC.eq, lines_ofList, List.map_map]
  rfl

private theorem card_fin_filter (n : Nat) (g : Nat → Bool) :
    (Finset.univ.filter fun p : Fin n => g p.val = true).card =
      ((List.range n).filter g).length := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun p => if g p = true then 1 else 0) n,
    ← Finset.card_filter]
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe]

private theorem card_class (i : Fin 5) :
    (Finset.univ.filter fun p : Fin 1755 => labFin 1755 5 (by norm_num) titsLabels p = i).card =
      [1, 10, 80, 640, 1024].getD i.val 0 := by
  have e : Finset.univ.filter (fun p : Fin 1755 => labFin 1755 5 (by norm_num) titsLabels p = i) =
      Finset.univ.filter fun p : Fin 1755 =>
        Nat.beq (CFSG.KC.TitsOuter.labAt (TitsLbT.F 0) p.val % 5) i.val = true := by
    apply Finset.filter_congr
    intro p _
    have hv : (labFin 1755 5 (by norm_num) titsLabels p).val = titsLabels[p.val]! % 5 := rfl
    rw [Fin.ext_iff, hv, labels_get p.2, Nat.beq_eq]
  rw [e]
  refine (card_fin_filter 1755
    (fun x => Nat.beq (CFSG.KC.TitsOuter.labAt (TitsLbT.F 0) x % 5) i.val)).trans ?_
  have h := congrArg (fun l : List Nat => l.getD i.val 0) cnt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2,
    Option.map_some, Option.getD_some] at h
  exact h

private theorem labels_div : LabelsDivisorOK 1755 5 (by norm_num) titsLabels ⟨0, by norm_num⟩ := by
  have h0 : labFin 1755 5 (by norm_num) titsLabels ⟨0, by norm_num⟩ = 0 := by
    apply Fin.ext
    have hv : (labFin 1755 5 (by norm_num) titsLabels ⟨0, by norm_num⟩).val =
        titsLabels[0]! % 5 := rfl
    rw [hv, labels_get (by norm_num)]
    decide +kernel
  have key : ∀ T : Finset (Fin 5), (0 : Fin 5) ∈ T →
      (∑ i ∈ T, [1, 10, 80, 640, 1024].getD i.val 0) ∣ 1755 → T = {0} ∨ T = Finset.univ := by
    decide +kernel
  intro T hT hd
  rw [h0] at hT ⊢
  simp only [card_class, Fintype.card_fin] at hd
  exact key T hT hd

private theorem powA_G {p : Nat} (hp : Gd p) (k : Nat) :
    powA 1755 (unpack 1755 11 p) k = unpack 1755 11 (ppw p k) :=
  pow_G hp (by rw [powA]) (fun _ => by rw [powA]) k

private theorem beq_false {x y : Nat} (h : bIf(Nat.beq x y, false, true) = true) :
    Nat.beq x y = false := by
  cases e : Nat.beq x y
  · rfl
  · rw [e] at h
    exact absurd h Bool.false_ne_true

end CertificateChecks.Batch8077

end
