module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import Certificates.Kernel.Misc.Coset.SuzTabA.All
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalComp.SurjGen
public import CFSG.Certificates.Kernel.CosetJ.WordsTSound
public import CFSG.Certificates.Kernel.MtxKSound
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermRep
public import Certificates.Kernel.CosetJ.Cover
public import Certificates.Kernel.Bounds.Suz.Binding
import Certificates.Kernel.CosetJ.Suz
import Certificates.Kernel.CosetJ.RhoPerm
import CFSG.Sporadic.Recognition.CoverTransferWords
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.Sporadic.SuzOddCore.Arrays
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all CFSG.Certificates.CosetTablePresented
import all CFSG.Sporadic.Presentation.SuzInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
meta import CFSG.Sporadic.SuzOddCore.Text
meta import Certificates.Data.CFSGNative.Bridge.SuzGPL
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Presentation.Common

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelCosetJ.SuzTabM1 CFSG.Sporadic.SuzOddCore.suzP1782M1Text
#ks_chars CertificateChecks.KernelCosetJ.SuzTabM2 CFSG.Sporadic.SuzOddCore.suzP1782M2Text
#ks_chars CertificateChecks.KernelCosetJ.SuzTabIT CFSG.Sporadic.Bridge.SuzGPL.Native.imgText
#ks_chars CertificateChecks.KernelCosetJ.SuzTabST CFSG.Sporadic.Bridge.SuzGPL.Native.surjText
#lc_words CertificateChecks.KernelCosetJ.SuzTabIT CFSG.Sporadic.Bridge.SuzGPL.Native.imgText
#lc_words CertificateChecks.KernelCosetJ.SuzTabST CFSG.Sporadic.Bridge.SuzGPL.Native.surjText
#kc_repo #kc_nat_items_gz CFSG.KD.CJSuzTab "Certificates/Kernel/CosetJ/data/consts.items.gz" 4910 18034802032098508815
  PB[2]

namespace CertificateChecks.KernelCosetJ.SuzTab

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Bridge.SuzGPL.Native CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (Rep eqA_iff rep_idA getElem!_ofFn_nat allLt_iff toLetters)

instance : NeZero gcS := ⟨by decide⟩

private theorem gcS_eq : gcS = 7 := by decide

theorem img_eq : imgWords = SuzTabIT.W.toArray := by
  have h := CFSG.KC.WordsT.wordsT_sound (cs := SuzTabIT.chars) (L := SuzTabIT.W) (by quickRfl)
  rw [← SuzTabIT.eq] at h
  exact h

theorem surj_eq : surjWords = SuzTabST.W.toArray := by
  have h := CFSG.KC.WordsT.wordsT_sound (cs := SuzTabST.chars) (L := SuzTabST.W) (by quickRfl)
  rw [← SuzTabST.eq] at h
  exact h

theorem img_forged_rejected : Act.notB (CFSG.KC.WordsT.wordsT SuzTabIT.chars
    (((SuzTabIT.W.headD []).dropLast ++ [7]) :: SuzTabIT.W.tail)) = true := by
  quickRfl

theorem strict_rejects : Act.notB (CFSG.KC.SurjK.wordsK SuzTabST.chars SuzTabST.W) = true := by
  quickRfl

@[expose] def bL (j : Fin 2) : Fin 9 := ⟨j.val, by omega⟩

@[expose] def gL (i : Fin 7) : Fin 9 := ⟨i.val + 2, by omega⟩

def shL (i : Fin gcS) : Fin 9 := ⟨i.val + 2, by have := lt_of_lt_of_eq i.2 gcS_eq; omega⟩

def shW (w : List (Fin gcS × Bool)) : List (Fin 9 × Bool) := w.map fun l => (shL l.1, l.2)

def tabWs : List (List (Fin 9 × Bool)) :=
  (List.finRange 7).map (fun i => (gL i, false) ::
      (toLetters 2 imgWords[i.val]!).map fun l => (bL l.1, l.2)) ++
    suzTabWords.map shW ++
    (List.finRange 2).map (fun k => (bL k, false) ::
      (toLetters 7 surjWords[k.val]!).map fun l => (gL l.1, l.2))

theorem hrels : tabWs.map Act.revCodes = CFSG.KAct.SuzTab.rels := by
  rw [tabWs, img_eq, surj_eq, suzTabWords, Suz.R0_eq]
  decide +kernel

theorem himg : imgWords.size = 7 ∧ imgWords.all (lettersOK 2) = true ∧ surjWords.size = 2 ∧
    lettersOK 7 surjWords[0]! = true ∧ lettersOK 7 surjWords[1]! = true := by
  rw [img_eq, surj_eq]
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have h : ∀ w ∈ SuzTabIT.W, lettersOK 2 w = true := by decide +kernel
  rw [Array.all_eq_true]
  intro i hi
  simp only [List.getElem_toArray]
  exact h _ (List.getElem_mem _)

theorem hletters : ∀ w ∈ suzTabWords, lettersOK gcS (zword w) = true := by
  rw [suzTabWords, Suz.R0_eq]
  decide +kernel

theorem bind : Act.allR 0 1782 (fun x => Act.andB
    (Nat.beq (CFSG.KAct.SuzTab.A (x * (9 + 9) + 2 * 0)) (pg 11 (mask 11) CFSG.KD.CJSuzTab.PB0 x))
    (Nat.beq (CFSG.KAct.SuzTab.A (x * (9 + 9) + 2 * 1)) (pg 11 (mask 11) CFSG.KD.CJSuzTab.PB1 x))) =
    true := by
  quickRfl

theorem b0_eq : b0Arr = unpack 1782 11 CFSG.KD.CJSuzTab.PB0 := by
  rw [b0Arr, SuzTabM1.eq]
  exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)

theorem b1_eq : b1Arr = unpack 1782 11 CFSG.KD.CJSuzTab.PB1 := by
  rw [b1Arr, SuzTabM2.eq]
  exact CFSG.KC.Mtx.mtxK_sound (by quickRfl)

theorem fix_d :
    CFSG.CosetTable.countBelow (fun x => CFSG.KAct.SuzTab.A (x * (9 + 9) + 2 * 5) == x) 1782 =
      42 := by
  decide +kernel

theorem countGo_congr {p q : ℕ → Bool} : ∀ n acc, (∀ i < n, p i = q i) →
    CFSG.CosetTable.countBelowAux p n acc = CFSG.CosetTable.countBelowAux q n acc
  | 0, _, _ => rfl
  | n + 1, acc, h => by
    simp only [CFSG.CosetTable.countBelowAux, h n (by omega)]
    exact countGo_congr n _ fun i hi => h i (by omega)

theorem signedProd_map {G : Type*} [Group G] {m k : ℕ} (σ : Fin m → G) (f : Fin k → Fin m)
    (w : List (Fin k × Bool)) :
    signedProd σ (w.map fun l => (f l.1, l.2)) = signedProd (fun h => σ (f h)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.map_cons, signedProd_cons, signedProd_cons, ih]

theorem wordIn_eq {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    wordIn k gs w = signedProd (fun h : Fin k => gs h) (toLetters k w) := by
  rw [wordIn, Quiver.SchreierGraph.evalWord, lift_mk_eq_signedProd]

theorem check : suzTabCheck = true := by
  have hpt := Act.pointOK_of_allR CFSG.KAct.SuzTab.all
  obtain ⟨σ, hσ⟩ := Act.exists_rep hpt
  have hw := Act.relsAt_sound hσ tabWs hrels (fun x hx => Act.relsAt_of_pointOK (hpt x hx))
  have hb := Act.allR_spec bind
  obtain ⟨hsz, hil, hssz, hs0, hs1⟩ := himg
  let bs : ℕ → Equiv.Perm (Fin 1782) := fun j => if h : j < 2 then σ (bL ⟨j, h⟩) else 1
  have hbs : ∀ j < 2, Rep 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[j]! (bs j) := by
    intro j hj x
    have hx := hb x.val (Nat.zero_le _) (by simp)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    simp only [bs, hj, ↓reduceDIte]
    have hr := (hσ (bL ⟨j, hj⟩) x).1
    have e0 : (#[b0Arr, b1Arr] : Array (Array ℕ))[0]! = b0Arr := rfl
    have e1 : (#[b0Arr, b1Arr] : Array (Array ℕ))[1]! = b1Arr := rfl
    interval_cases j
    · rw [e0, b0_eq, unpack, getElem!_ofFn_nat _ x.2]
      exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · rw [e1, b1_eq, unpack, getElem!_ofFn_nat _ x.2]
      exact (Nat.eq_of_beq_eq_true hx.2).symm.trans hr
  have hbsI : ∀ j < 2, isInvA 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[j]!
      (invCand 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[j]!) = true :=
    fun j hj => RhoPerm.isInvA_of_rep (hbs j hj)
  let gs : ℕ → Equiv.Perm (Fin 1782) := fun i => if h : i < 7 then σ (gL ⟨i, h⟩) else 1
  have hgw : ∀ i (hi : i < 7), wordIn 2 bs imgWords[i]! = gs i := by
    intro i hi
    have h1 := hw _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩)))
    rw [signedProd_cons, signedProd_map] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    have hf : (fun h : Fin 2 => bs h) = fun h => σ (bL h) := by
      funext h
      simp only [bs, h.2, ↓reduceDIte, Fin.eta]
    rw [wordIn_eq, hf]
    simp only [gs, hi, ↓reduceDIte]
    exact (inv_mul_eq_one.1 h1).symm
  have hgs : ∀ i < 7, Rep 1782 suzGenArrs[i]! (gs i) := by
    intro i hi
    have hi' : i < imgWords.size := by rw [hsz]; exact hi
    have e : suzGenArrs[i]! = wordArr 1782 #[b0Arr, b1Arr] imgWords[i]! := by
      rw [suzGenArrs, getElem!_pos _ i (by rw [Array.size_map]; exact hi'), Array.getElem_map,
        getElem!_pos imgWords i hi']
    rw [e, ← hgw i hi]
    refine rep_wordArr (by decide) hbs hbsI ?_
    rw [getElem!_pos imgWords i hi']
    exact (Array.all_eq_true.1 hil) i hi'
  have hgsI : ∀ i < 7, isInvA 1782 suzGenArrs[i]! (invCand 1782 suzGenArrs[i]!) = true :=
    fun i hi => RhoPerm.isInvA_of_rep (hgs i hi)
  have hgsize : suzGenArrs.size = 7 := by rw [suzGenArrs, Array.size_map, hsz]
  have hval : ∀ w : List (Fin gcS × Bool), wordIn gcS gs (zword w) = signedProd σ (shW w) := by
    intro w
    rw [← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_eq_wordIn, lift_mk_eq_signedProd, shW,
      signedProd_map]
    congr 1
    funext i
    have hi : (i : ℕ) < 7 := lt_of_lt_of_eq i.2 gcS_eq
    simp only [gs, hi, ↓reduceDIte]
    rfl
  have hsurj : ∀ k (hk : k < 2), wordIn 7 gs surjWords[k]! = bs k := by
    intro k hk
    have h1 := hw _ (List.mem_append_right _ (List.mem_map.2 ⟨⟨k, hk⟩, List.mem_finRange _, rfl⟩))
    rw [signedProd_cons, signedProd_map] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    have hf : (fun h : Fin 7 => gs h) = fun h => σ (gL h) := by
      funext h
      simp only [gs, h.2, ↓reduceDIte, Fin.eta]
    rw [wordIn_eq, hf]
    simp only [bs, hk, ↓reduceDIte]
    exact (inv_mul_eq_one.1 h1).symm
  have hrepS : ∀ k (hk : k < 2), Rep 1782 (wordArr 1782 suzGenArrs surjWords[k]!) (bs k) := by
    intro k hk
    rw [← hsurj k hk]
    refine rep_wordArr (by rw [hgsize]) hgs hgsI ?_
    interval_cases k
    · exact hs0
    · exact hs1
  unfold suzTabCheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hsz⟩, hil⟩, ?_⟩, fun w hwm => ⟨hletters w hwm, ?_⟩⟩, hssz⟩, hs0⟩, hs1⟩,
    ?_⟩, ?_⟩, ?_⟩
  · rw [allPermsOK, allLt_iff]
    exact hbsI
  · rw [allPermsOK, hgsize, allLt_iff]
    exact hgsI
  · have hl := hletters w hwm
    rw [eqA_iff (rep_wordArr (by rw [hgsize, gcS_eq]) (fun i hi => hgs i (gcS_eq ▸ hi))
      (fun i hi => hgsI i (gcS_eq ▸ hi)) hl) rep_idA, hval]
    exact hw _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hwm)))
  · exact (eqA_iff (hrepS 0 (by decide)) (hbs 0 (by decide))).2 rfl
  · exact (eqA_iff (hrepS 1 (by decide)) (hbs 1 (by decide))).2 rfl
  · have hc : ∀ x < 1782, ((suzGenArrs[3]!)[x]! == x) =
        (CFSG.KAct.SuzTab.A (x * (9 + 9) + 2 * 5) == x) := by
      intro x hx
      have h3 : (3 : ℕ) < 7 := by decide
      have hr : CFSG.KAct.SuzTab.A (x * (9 + 9) + 2 * 5) = (σ (gL ⟨3, h3⟩) ⟨x, hx⟩ : ℕ) :=
        (hσ (gL ⟨3, h3⟩) ⟨x, hx⟩).1
      rw [(hgs 3 h3).apply hx, hr]
      simp only [gs, h3, ↓reduceDIte]
    rw [CFSG.CosetTable.countBelow, countGo_congr 1782 0 hc]
    exact fix_d

end CertificateChecks.KernelCosetJ.SuzTab

end
