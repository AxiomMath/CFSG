module

public import CFSG.Quasithin.Recognition.CertPermOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsOuterInputs
import Certificates.Certificate8071
import Certificates.Certificate8072
import Certificates.Kernel.Misc.Tits.Outer8075
import Certificates.Kernel.Misc.Tits.Pi7092Neg
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Misc.TitsPiSound
import CFSG.Certificates.Kernel.Misc.TitsOuterSound
import CFSG.Certificates.Kernel.Spor.RawSiftKConv
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.YModel.Sound
import CFSG.Sporadic.Schreier.TitsChain
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor.Tits2264

namespace CertificateChecks.Batch8075

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor.Tits2264

private theorem gens_eq {j : Nat} (hj : j < 2) : titsGens[j]! = titsDerivedArrs[j]! := by
  interval_cases j
  · exact Certificates.certificate8072.1
  · exact Certificates.certificate8072.2

private theorem sizeD : titsDerivedArrs.size = 13 := by simp [titsDerivedArrs, titsField1755]

private theorem allPermsD : allPermsOK 1755 titsDerivedArrs = true :=
  allPerms_of sizeD (fun _ hj => der_eq hj) permD

private theorem rep_d {j : Nat} (hj : j < 2) : Rep 1755 titsGens[j]! (d j) := by
  rw [gens_eq hj]
  exact (rep_permOfArr (isInvA_of_allPermsOK allPermsD (by
    rw [sizeD]
    omega))).1

private theorem inv_d {j : Nat} (hj : j < 2) :
    isInvA 1755 titsGens[j]! (invCand 1755 titsGens[j]!) = true := by
  rw [gens_eq hj]
  exact isInvA_of_allPermsOK allPermsD (by
    rw [sizeD]
    omega)

private theorem allPerms_of_chain {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (h : rawChainOK n O S base W chunks = true) :
    allPermsOK n S = true := by
  unfold rawChainOK at h
  simp only [Bool.and_eq_true] at h
  have h3 := h.1.1.1.1.1.1.2
  unfold allPermsOK
  rw [allLt_iff] at h3 ⊢
  intro j hj
  have := h3 j hj
  rwa [rawInvs, getElem!_map_of_lt hj] at this

private theorem base_eq : (titsBase.map Fin.val).toArray = baseArr 1755 (titsBase.map Fin.val) := by
  decide

private theorem strong_get {j : Nat} (hj : j < 2) : titsStrong[j]! = titsDerivedArrs[j]! := by
  rw [Certificates.certificate8071.2.2.2.1 j hj, gens_eq hj]

private theorem sift_iff {g : Array ℕ} {G : Equiv.Perm (Fin 1755)} (hG : Rep 1755 g G) :
    titsSift g = true ↔ G ∈ T := by
  have hc := Certificates.certificate8071.2.2.2.2.1
  have hk : titsGens.size ≤ titsStrong.size := Certificates.certificate8071.2.2.1
  unfold titsSift
  rw [base_eq] at hc ⊢
  rw [siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := hk) (hb := by decide)
    (allPerms_of_chain hc) (by norm_num) hc hG, originalSubgroup_ofArrays]
  have e : (fun i : Fin titsGens.size => permOfArr 1755 titsStrong[(i : ℕ)]!) =
      fun i : Fin 2 => d i.val := by
    funext i
    rw [strong_get i.2]
    rfl
  rw [e]
  rfl

private theorem textLines_nl (cs : List Char) :
    CFSG.YGroups.ModelNative.textLines (String.ofList ('\n' :: cs)) =
      CFSG.YGroups.ModelNative.textLines (String.ofList cs) := by
  rw [CFSG.KS.DecLines.textLines_ofList, CFSG.KS.DecLines.textLines_ofList,
    List.splitOnP_cons_eq_ite_modifyHead]
  simp

private theorem textLines_zero (cs : List Char) :
    CFSG.YGroups.ModelNative.textLines (String.ofList ('0' :: '\n' :: cs)) =
      "0" :: CFSG.YGroups.ModelNative.textLines (String.ofList cs) := by
  rw [CFSG.KS.DecLines.textLines_ofList, CFSG.KS.DecLines.textLines_ofList,
    List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead]
  simp

private theorem ab_chars : TitsAbC.chars = '\n' :: TitsAbC.chars.tail := by decide +kernel

private theorem words_eq : titsAbWords = (CFSG.KC.YModel.linesW (CFSG.KC.YModel.lget TitsAbT.El) 32
    (fun L => CFSG.KC.YModel.joinW 32 (CFSG.KC.YModel.lgetL TitsAbT.Cl L)) TitsAbT.lines).toList := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsAbT.ok).2
  rw [← CFSG.KC.YModel.charsOf_eq, TitsOut.abChars, ab_chars] at h
  unfold CFSG.YGroups.ModelNative.chainWords at h
  rw [textLines_zero] at h
  rw [titsAbWords, TitsAbC.eq, ab_chars, textLines_nl, ← h]
  simp

private theorem letters₀ : lettersOK 2 (titsAbWords.getD 0 []) = true := by
  rw [words_eq]
  decide +kernel

private theorem letters₁ : lettersOK 2 (titsAbWords.getD 1 []) = true := by
  rw [words_eq]
  decide +kernel

private theorem word_mem {w : List ℤ} (hw : lettersOK 2 w = true) :
    titsSift (wordA 1755 titsGens (rawInvs 1755 titsGens) w) = true := by
  have hr : Rep 1755 (wordArr 1755 titsGens w) (wordIn 2 d w) :=
    rep_wordArr (by decide) (fun i hi => rep_d hi) (fun i hi => inv_d hi) hw
  exact (sift_iff hr).2 (CFSG.KS.PresPG.wordIn_mem_closure 2 d w)

private theorem pi_eq : titsPiArr = unpack 1755 11 TitsPi.P :=
  CFSG.KC.TitsPi.cmpL_sound TitsPi.bind

private theorem conj_eq {j : Nat} (hj : j < 2) {s : String}
    (hs : titsArray s = titsDerivedArrs[j]!) :
    compA 1755 (compA 1755 titsPiArr (titsArray s)) (invCand 1755 titsPiArr) =
      unpack 1755 11 (TitsOut.cj j) := by
  have hP := permC_spec TitsPi.perm
  have hD := permC_spec (permD_spec j hj)
  rw [hs, der_eq (by omega), pi_eq, CFSG.KC.BfsPin.invCand_unpack hP.1,
    CFSG.KC.BfsPin.compA_unpack hP.2.1 hD.2.1,
    CFSG.KC.BfsPin.compA_unpack (CFSG.KC.BfsPin.canonK_pcomp hP.2.1 hD.2.1) hP.2.2]
  rfl

private theorem conj_sift {j : Nat} (hj : j < 2) {s : String}
    (hs : titsArray s = titsDerivedArrs[j]!) :
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray s)) (invCand 1755 titsPiArr)) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec TitsOut.conj j hj)
  rw [conj_eq hj hs]
  exact (sift_iff (rep_of h2).1).2 (mem_T h1 h2)

private theorem pi_not_mem : permOfArr 1755 (unpack 1755 11 TitsPi.P) ∉ T := by
  intro hm
  have hP := permC_spec TitsPi.perm
  have hf := CFSG.KS.Raw.Orb.siftA_false_of_K bindsD permD KernelSpor.TitsD.hl (by decide)
    (hiOf hP.2.1) (range_of_permOK hP.1) TitsPi.neg_sift
  have ht := (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [sizeD]; norm_num) (hb := by decide) (chunks := 4)
    allPermsD (by norm_num) chainD (rep_of TitsPi.perm).1).2 (by
      rw [originalSubgroup_ofArrays]
      exact hm)
  rw [hf] at ht
  exact absurd ht Bool.false_ne_true

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

private theorem labels_ok : titsLabelsNontrivial = true := by
  unfold titsLabelsNontrivial
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_range] at hp
  by_cases h0 : p = 0
  · simp [h0]
  obtain ⟨q, hq, hne, he⟩ := CFSG.KC.TitsOuter.labOK_sound TitsOut.lab p hp h0
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨q, hq, hne, by rw [labels_get hq, labels_get hp, he]⟩

private theorem titsOuter_check_0 :
    isInvA 1755 titsPiArr (invCand 1755 titsPiArr) = true ∧
    titsSift titsA = true ∧ titsSift titsB = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData1))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData2))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift titsPiArr = false ∧ titsLabelsNontrivial = true := by
  refine ⟨?_, word_mem letters₀, word_mem letters₁, conj_sift (j := 0) (by norm_num)
    Certificates.certificate8072.1, conj_sift (j := 1) (by norm_num) Certificates.certificate8072.2, ?_,
    labels_ok⟩
  · rw [pi_eq]
    exact isInv_of TitsPi.perm
  · cases h : titsSift titsPiArr
    · rfl
    · rw [pi_eq] at h
      exact absurd ((sift_iff (rep_of TitsPi.perm).1).1 h) pi_not_mem

end CertificateChecks.Batch8075

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native in
theorem certificate8075 :
    isInvA 1755 titsPiArr (invCand 1755 titsPiArr) = true ∧
    titsSift titsA = true ∧ titsSift titsB = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData1))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift (compA 1755 (compA 1755 titsPiArr (titsArray CFSG.Open.quasithinTitsData2))
      (invCand 1755 titsPiArr)) = true ∧
    titsSift titsPiArr = false ∧ titsLabelsNontrivial = true := by
  exact CertificateChecks.Batch8075.titsOuter_check_0

end Certificates

end
