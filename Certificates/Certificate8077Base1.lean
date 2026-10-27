
module

public import Certificates.Certificate8077Base
import all Certificates.Certificate8077Base

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
import Certificates.Kernel.Misc.Tits.Strong8077
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

private theorem orbits : rawOrbitSizes 1755 titsPairStrong (titsPairBase.map Fin.val).toArray =
    [1755, 10, 8, 2, 8, 4, 2] := by
  have h := rawOrbitSizesK_orb (NS := 28) (CH := 64) (LR := TitsPCh.LR) (PSI := TitsPCh.SI) binds
    perms TitsPCh.ho (by norm_num)
  have e : (List.range 7).map (fun i => rcnt (TitsPCh.LR i)) = [1755, 10, 8, 2, 8, 4, 2] := by
    decide +kernel
  exact h.trans e

private theorem isInv_d {j : Nat} (hj : j < 2) :
    isInvA 1755 titsGens[j]! (invCand 1755 titsGens[j]!) = true := by
  rw [gens_get.2 j hj, invCand_G (Gd_DS j)]
  exact isInvA_G (Gd_DS j)

private theorem rep_d {j : Nat} (hj : j < 2) : Rep 1755 titsGens[j]! (d j) := by
  have e : titsGens[j]! = CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[j]! := by
    rw [gens_get.2 j hj, derived_get (by omega)]
  have h := (rep_permOfArr (isInv_d hj)).1
  rw [e] at h ⊢
  exact h

private theorem isInvA_A : isInvA 1755 titsA (invCand 1755 titsA) = true := by
  rw [a_eq, invCand_G gdA]
  exact isInvA_G gdA

private theorem isInvA_B : isInvA 1755 titsB (invCand 1755 titsB) = true := by
  rw [b_eq, invCand_G gdB]
  exact isInvA_G gdB

private theorem mem_word {k : Nat} (hl : lettersOK 2 (titsAbWords.getD k []) = true)
    (hi : isInvA 1755 (wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD k []))
      (invCand 1755 (wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD k []))) =
        true) :
    permOfArr 1755 (wordA 1755 titsGens (rawInvs 1755 titsGens) (titsAbWords.getD k [])) ∈ T := by
  have hr : Rep 1755 (CFSG.Sporadic.Schreier.Tits.wordArr 1755 titsGens (titsAbWords.getD k []))
      (CFSG.Sporadic.Schreier.Tits.wordIn 2 d (titsAbWords.getD k [])) :=
    CFSG.Sporadic.Schreier.Tits.rep_wordArr (by rw [gens_get.1]) (fun i hi => rep_d hi)
      (fun i hi => isInv_d hi) hl
  rw [Rep.unique (rep_permOfArr hi).1 hr]
  exact CFSG.KS.PresPG.wordIn_mem_closure 2 d _

private theorem card_le : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 1755 titsPairStrong[j.val]!)) ≤ (rawOrbitSizes 1755 titsPairStrong
      (titsPairBase.map Fin.val).toArray).prod := by
  have hle : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 1755 titsPairStrong[j.val]!) ≤
      T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    change permOfArr 1755 titsPairStrong[j.val]! ∈ T
    have e : titsPairStrong[j.val]! = titsPairO[j.val]! := by
      rw [strong_get.2 j.val (by omega), pair_get.2 j.val j.2]
    rw [e]
    rcases j with ⟨_ | _ | j, hj⟩
    · exact mem_word letters₀ isInvA_A
    · exact mem_word letters₁ isInvA_B
    · omega
  rw [orbits]
  exact (Subgroup.card_le_of_le hle).trans (card_T.trans (by norm_num))

private theorem chain : rawChainOK 1755 (titsPairStrong.extract 0 titsPairO.size) titsPairStrong
    (titsPairBase.map Fin.val).toArray titsPairRawWords 4 = true := by
  rw [pair_get.1, words_raw]
  exact rawChainK_of_card_orb 4 binds TitsPCh.head TitsPCh.ho (by norm_num : 1755 ≤ 28 * 64)
    card_le

private theorem prim : primCheck 1755 titsPairStrong 0 titsLabels titsRoots 5 titsTw titsHw =
    true := by
  rw [tw_eq, hw_eq]
  exact primCheck_of_walk strong_get.1 strong_get.2 (CFSG.KS.Raw.Orb.allN_iff.1 perms)
    (fun p hp => labels_get hp) (fun i hi => roots_get hi) (by norm_num) walk

private theorem titsPair_check_0 :
    isInvA 1755 titsA (invCand 1755 titsA) = true ∧
    isInvA 1755 titsB (invCand 1755 titsB) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 0 []) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 1 []) = true ∧
    titsPairO.size ≤ titsPairStrong.size ∧
    (∀ i < titsPairO.size, titsPairStrong[i]! = titsPairO[i]!) ∧
    rawChainOK 1755 (titsPairStrong.extract 0 titsPairO.size) titsPairStrong
      (titsPairBase.map Fin.val).toArray titsPairRawWords 4 = true ∧
    rawOrbitSizes 1755 titsPairStrong (titsPairBase.map Fin.val).toArray =
      [1755, 10, 8, 2, 8, 4, 2] ∧
    primCheck 1755 titsPairStrong 0 titsLabels titsRoots 5 titsTw titsHw = true ∧
    eqA 1755 (powA 1755 titsA 2) (idA 1755) = true ∧ eqA 1755 titsA (idA 1755) = false ∧
    eqA 1755 (powA 1755 titsB 3) (idA 1755) = true ∧ eqA 1755 titsB (idA 1755) = false ∧
    eqA 1755 (powA 1755 (compA 1755 titsA titsB) 13) (idA 1755) = true ∧
    eqA 1755 (compA 1755 titsA titsB) (idA 1755) = false := by
  obtain ⟨oa1, oa2⟩ := @split (Nat.beq (ppw A 2) pe) (bIf(Nat.beq A pe, false, true)) ordA
  obtain ⟨ob1, ob2⟩ := @split (Nat.beq (ppw B 3) pe) (bIf(Nat.beq B pe, false, true)) ordB
  obtain ⟨oc1, oc2⟩ := @split (Nat.beq (ppw (pm A B) 13) pe)
    (bIf(Nat.beq (pm A B) pe, false, true)) ordAB
  refine ⟨isInvA_A, isInvA_B, by rw [gens_get.1]; exact letters₀,
    by rw [gens_get.1]; exact letters₁, by rw [pair_get.1, strong_get.1]; norm_num,
    fun i hi => by rw [pair_get.1] at hi; rw [strong_get.2 i (by omega), pair_get.2 i hi],
    chain, orbits, prim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq, powA_G gdA, idA_G, eqA_G (gdA.pow 2) Gd.one]
    exact oa1
  · rw [a_eq, idA_G, eqA_G gdA Gd.one]
    exact beq_false oa2
  · rw [b_eq, powA_G gdB, idA_G, eqA_G (gdB.pow 3) Gd.one]
    exact ob1
  · rw [b_eq, idA_G, eqA_G gdB Gd.one]
    exact beq_false ob2
  · rw [a_eq, b_eq, compA_G gdA gdB, powA_G (gdA.mul gdB), idA_G,
      eqA_G ((gdA.mul gdB).pow 13) Gd.one]
    exact oc1
  · rw [a_eq, b_eq, compA_G gdA gdB, idA_G, eqA_G (gdA.mul gdB) Gd.one]
    exact beq_false oc2

end CertificateChecks.Batch8077

end
