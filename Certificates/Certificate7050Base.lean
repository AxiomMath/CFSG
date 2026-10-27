
module

public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public import CFSG.Quasithin.Recognition.RuRank3Tits13Base
import CFSG.Sporadic.Schreier.TitsCertCheckInputs
import Certificates.Kernel.EvenBN.CNtEq
import Certificates.Kernel.Misc.Tits.Cls7050S0
import Certificates.Kernel.Misc.Tits.Cls7050S1
import Certificates.Kernel.Misc.Tits.Cls7050S2
import Certificates.Kernel.Misc.Tits.Cls7050S3
import Certificates.Kernel.Misc.Tits.Cls7050S4
import Certificates.Kernel.Misc.Tits.Cls7050S5
import Certificates.Kernel.Misc.Tits.Cls7050S6
import Certificates.Kernel.Misc.Tits.Cls7050S7
import Certificates.Kernel.Misc.Tits.Cls7050S8
import Certificates.Kernel.Misc.Tits.Cls7050S9
import Certificates.Kernel.Misc.Tits.Cls7050S10
import Certificates.Kernel.Misc.Tits.Cls7050S11
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Misc.Tits.Bad7050
import Certificates.Kernel.Misc.Tits.K0Use7050
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawSiftKConv
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Sporadic.Schreier.TitsCert
import CFSG.Sporadic.Schreier.TitsCertCheck
import CFSG.Sporadic.Schreier.TitsChain
import Certificates.Kernel.Misc.Tits.K0Chain7050

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelMisc CertificateChecks.KernelMisc.Tits7050
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CFSG.KS.Raw.Orb (bIf_eq unpack_get)

namespace CertificateChecks.Batch7050

private abbrev Cn (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

private theorem szOK' : szOK 1755 11 = true := by decide

private theorem cId : Cn (pidn 1755 11) := (CFSG.KC.BfsPin.PP.id szOK').1

private theorem idA_eq' : idA 1755 = unpack 1755 11 (pidn 1755 11) := CFSG.KC.BfsPin.idA_eq szOK'

private theorem cmp {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

private theorem cmpC {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

private theorem eqU {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

private theorem powU {p : Nat} (hp : Cn p) :
    ∀ k, powArr 1755 (unpack 1755 11 p) k = unpack 1755 11 (pw p k) ∧ Cn (pw p k)
  | 0 => ⟨idA_eq', cId⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := powU hp k
    refine ⟨?_, cmpC hp h2⟩
    rw [powArr, h1, cmp hp h2]
    rfl

private theorem cOf {P : Nat} (h : permC P = true) : Cn P := (permC_spec h).2.1

private theorem invU {P : Nat} (h : permC P = true) :
    invCand 1755 (unpack 1755 11 P) = unpack 1755 11 (pinvS 1755 11 (mask 11) P) :=
  CFSG.KC.BfsPin.invCand_unpack (permC_spec h).1

private theorem perms4 : permC Aux = true ∧ permC Y = true ∧ permC X = true ∧ permC TitsT = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff (permC Aux) _).1 perms
  obtain ⟨h2, h⟩ := (bAnd_iff (permC Y) _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff (permC X) (permC TitsT)).1 h
  exact ⟨h1, h2, h3, h4⟩

private theorem pAux : permC Aux = true := perms4.1
private theorem pY : permC Y = true := perms4.2.1
private theorem pX : permC X = true := perms4.2.2.1
private theorem pT : permC TitsT = true := perms4.2.2.2
private theorem pR {i : Nat} (hi : i < 30) : permC (R i) = true := allN_spec permR i hi
private theorem pK {j : Nat} (hj : j < 5) : permC (TK.F j) = true := allN_spec permK j hj

private theorem aux_eq : titsAuxArr = unpack 1755 11 Aux := KernelEvenBN.aux_eq

private theorem t_eq : titsTArr = unpack 1755 11 TitsT := TitsInv.t_eq

private theorem y_eq : titsY12Arr = unpack 1755 11 Y := by
  change hexTable 3 1755 (1755 * 0) titsY12Text = _
  rw [TY.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TY.all 0 (by norm_num)

private theorem x_eq : titsX13Arr = unpack 1755 11 X := by
  change hexTable 3 1755 (1755 * 0) titsX13Text = _
  rw [TX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TX.all 0 (by norm_num)

private theorem r_eq {i : Nat} (hi : i < 30) : titsRepArr i = unpack 1755 11 (R i) := by
  change hexTable 3 1755 (1755 * i) titsRepsText = _
  rw [TR.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TR.all i hi

private theorem k_eq {j : Nat} (hj : j < 5) : titsK0Strong[j]! = unpack 1755 11 (TK.F j) := by
  rw [titsK0Strong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 3 1755 (1755 * j) titsK0Text = _
  rw [TK.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TK.all j hj

private theorem T_le : T ≤ titsA := by
  unfold T
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact titsD_le_titsA (titsT_mem_titsD (i := j.val) (by omega))

private theorem t_mem : t ∈ titsA := by
  have e : t = titsGen 1 := by
    rw [titsGen, gen_eq (by norm_num)]
    rfl
  rw [e]
  exact titsGen_mem_titsA (by norm_num)

private theorem inA_of_mem {P : Nat} (hP : permC P = true)
    (hm : permOfArr 1755 (unpack 1755 11 P) ∈ titsA) : inTitsA (unpack 1755 11 P) = true := by
  rw [← titsQA_original] at hm
  exact (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsAmbientArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.1
    (rep_of hP).1).2 hm

private theorem inA_of_D {P : Nat} (hP : permC P = true) (hs : siftD P = true) :
    inTitsA (unpack 1755 11 P) = true :=
  inA_of_mem hP (T_le (mem_T hs hP))

private theorem inA_of_a {P : Nat} (hP : permC P = true)
    (hs : bAnd(siftD (pc P (GI 1)), permC (pc P (GI 1))) = true) :
    inTitsA (unpack 1755 11 P) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hs
  refine inA_of_mem hP ?_
  have hm := mem_T h1 h2
  rw [pc, perm_mul hP TitsPi.permGI h2] at hm
  have hinv : permOfArr 1755 (unpack 1755 11 (GI 1)) = t⁻¹ :=
    (rep_of TitsPi.permGI).1.unique (rep_of (gperm 1 (by norm_num))).2
  rw [hinv] at hm
  have h3 := mul_mem (T_le hm) t_mem
  rwa [inv_mul_cancel_right] at h3

private theorem notD_of {P : Nat} (hP : permC P = true) (hs : siftD P = false) :
    inTitsD (unpack 1755 11 P) = false :=
  CFSG.KS.Raw.Orb.siftA_false_of_K bindsD permD KernelSpor.TitsD.hl szOK'
    (hiOf (permC_spec hP).2.1) (range_of_permOK (permC_spec hP).1) hs

private theorem yl_spec {k : Nat} (hk : k < 12) :
    powArr 1755 titsY12Arr k = unpack 1755 11 (CFSG.KS.Mathieu.nget YL k) ∧
      invCand 1755 (powArr 1755 titsY12Arr k) = unpack 1755 11 (CFSG.KS.Mathieu.nget YIL k) ∧
      permC (CFSG.KS.Mathieu.nget YL k) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec yPow k hk)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  have e1 : powArr 1755 titsY12Arr k = unpack 1755 11 (CFSG.KS.Mathieu.nget YL k) := by
    rw [y_eq, (powU (cOf pY) k).1, Nat.eq_of_beq_eq_true h1]
  refine ⟨e1, ?_, h4⟩
  rw [e1, invU h4, Nat.eq_of_beq_eq_true h3]

private theorem isInvol_eq {P : Nat} (hP : Cn P) :
    isInvolA (unpack 1755 11 P) = (Nat.beq (pc P P) (pidn 1755 11) && !Nat.beq P (pidn 1755 11)) := by
  unfold isInvolA
  rw [cmp hP hP, idA_eq', eqU (cmpC hP hP) cId, eqU hP cId]

private theorem clsK_sound {P w : Nat} (hP : Cn P) (h : clsK P w = true) :
    classOK (unpack 1755 11 P) = true := by
  unfold clsK at h
  unfold classOK
  rw [Bool.or_eq_true, Bool.or_eq_true]
  cases h0 : Nat.beq w 0
  · rw [h0] at h
    dsimp only at h
    cases h1 : Nat.beq w 1
    · rw [h1] at h
      dsimp only at h
      rw [strictB_eq] at h
      simp only [show Nat.sub w 2 = w - 2 from rfl] at h
      obtain ⟨hk, hi⟩ := (bAnd_iff _ _).1 h
      have hk' := Nat.blt_eq.mp hk
      obtain ⟨i, hi30, hiE⟩ := List.any_eq_true.1 hi
      rw [List.mem_range] at hi30
      right
      unfold classifiedA
      rw [List.any_eq_true]
      refine ⟨w - 2, List.mem_range.2 hk', ?_⟩
      rw [List.any_eq_true]
      refine ⟨i, List.mem_range.2 hi30, ?_⟩
      obtain ⟨e1, e2, e3⟩ := yl_spec hk'
      have cYI : Cn (CFSG.KS.Mathieu.nget YIL (w - 2)) := by
        have h3 := ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (allN_spec yPow _ hk')).2).1
        rw [Nat.eq_of_beq_eq_true h3]
        exact (permC_spec e3).2.2
      rw [e2, e1, cmp (cOf e3) hP, cmp (cmpC (cOf e3) hP) cYI, r_eq hi30,
        eqU (cmpC (cmpC (cOf e3) hP) cYI) (cOf (pR hi30))]
      exact hiE
    · rw [h1] at h
      dsimp only at h
      left
      right
      rw [t_eq, eqU hP (cOf pT)]
      exact h
  · rw [h0] at h
    dsimp only at h
    left
    left
    unfold notInv at h
    cases e1 : Nat.beq P (pidn 1755 11)
    · rw [e1] at h
      dsimp only at h
      obtain ⟨x, hx, hxE⟩ := List.any_eq_true.1 h
      rw [List.mem_range] at hx
      have hne : pg 11 (mask 11) P (pg 11 (mask 11) P x) ≠ x := by
        intro e
        rw [e, Nat.beq_refl] at hxE
        exact absurd hxE Bool.false_ne_true
      unfold isInvolA
      rw [Bool.not_eq_true', Bool.and_eq_false_iff]
      left
      cases hq : eqA 1755 (compA 1755 (unpack 1755 11 P) (unpack 1755 11 P)) (idA 1755)
      · rfl
      · exfalso
        unfold eqA at hq
        rw [allLt_iff] at hq
        have := hq x hx
        have hpx := (CFSG.KS.PF.canon_facts hP).2.2.2 x hx
        rw [beq_iff_eq, compA_get hx, unpack_get hx, unpack_get hpx, idA_get hx] at this
        exact hne this
    · rw [isInvol_eq hP, Nat.eq_of_beq_eq_true e1, Nat.beq_refl]
      simp

private theorem cls2_sound {k w : Nat} (hk : Cn (KernelEvenBN.PN k)) (h : cls2 k w = true) :
    (classOK (unpack 1755 11 (KernelEvenBN.PN k)) &&
      classOK (compA 1755 titsAuxArr (unpack 1755 11 (KernelEvenBN.PN k)))) = true := by
  unfold cls2 at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq] at h2
  rw [Bool.and_eq_true, aux_eq, cmp (cOf pAux) hk]
  exact ⟨clsK_sound hk h1, clsK_sound (cmpC (cOf pAux) hk) h2⟩

private theorem chkL_spec {W : Nat → Nat} : ∀ (l : List Nat) (j : Nat), chkL W l j = true →
    ∀ m (hm : m < l.length), cls2 l[m] (W (j + m)) = true
  | [], _, _, m, hm => absurd hm (by simp)
  | k :: l, j, h, m, hm => by
    have h' : bAnd(cls2 k (W j), chkL W l (Nat.succ j)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    cases m with
    | zero => simpa using h1
    | succ m =>
      have := chkL_spec l (j + 1) h2 m (by simpa using hm)
      rw [List.getElem_cons_succ]
      rw [show j + (m + 1) = j + 1 + m by omega]
      exact this

private theorem slice_spec {s : Nat} (hs : chkL W ((KernelEvenBN.CNtC.drop (128 * s)).take 128)
    (128 * s) = true) {m : Nat} (hm1 : 128 * s ≤ m) (hm2 : m < 128 * s + 128)
    (hm : m < KernelEvenBN.CNtC.length) : cls2 KernelEvenBN.CNtC[m] (W m) = true := by
  have hl : m - 128 * s < ((KernelEvenBN.CNtC.drop (128 * s)).take 128).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have := chkL_spec _ _ hs (m - 128 * s) hl
  have e : ((KernelEvenBN.CNtC.drop (128 * s)).take 128)[m - 128 * s]'hl =
      KernelEvenBN.CNtC[m] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  rw [e, show 128 * s + (m - 128 * s) = m by omega] at this
  exact this

private theorem cls_all : ∀ m (hm : m < KernelEvenBN.CNtC.length),
    cls2 KernelEvenBN.CNtC[m] (W m) = true := by
  intro m hm
  have hl := KernelEvenBN.cnt_len
  have hs : ∀ s < 12, chkL W ((KernelEvenBN.CNtC.drop (128 * s)).take 128) (128 * s) = true := by
    intro s hs
    interval_cases s
    exacts [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  exact slice_spec (s := m / 128) (hs _ (by omega)) (by omega) (by omega) hm

private theorem cnt_ok : (titsCNt.all fun c => classOK c && classOK (compA 1755 titsAuxArr c)) = true := by
  rw [KernelEvenBN.cnt_eq, List.all_map, List.all_eq_true]
  intro k hk
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hk
  exact cls2_sound (KernelEvenBN.cnt_canon _ hk) (cls_all m hm)

private theorem bindsK : Binds 1755 11 TitsK0.S 5 3 TitsK0.BP titsK0Strong (ruBaseArr 1755 [0, 12, 1]) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [titsK0Strong], fun j hj => ?_, rfl,
    fun t ht => ?_⟩
  · rw [k_eq hj, Nat.eq_of_beq_eq_true (allN_spec kS j hj)]
  · rw [Nat.eq_of_beq_eq_true (allN_spec kB t ht)]
    interval_cases t <;> rfl

private theorem permsK :
    allN 5 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsK0.S j) (TitsK0.SI j)) = true :=
  (CFSG.KS.Raw.Orb.head_facts TitsK0.head).1

private theorem k0_chain : ruChainOK 1755 titsK0Strong 3 5 [0, 12, 1] titsK0Words = true :=
  rawChainK_sound bindsK TitsK0.head TitsK0.hl (by decide) TitsK0.hs

private theorem k0_orbits : rawOrbitSizes 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1]) = [975, 4, 2] := by
  rw [rawOrbitSizesK_sound bindsK permsK TitsK0.hl]
  decide +kernel

private theorem good_sift {i : Nat} (hi : i < 30)
    (h : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK0.LR TitsK0.TRI TitsK0.BP 3 0 (R i) =
      true) : inTitsK0 (titsRepArr i) = true := by
  rw [r_eq hi]
  exact siftK_soundR bindsK permsK TitsK0.hl rfl (hiOf (permC_spec (pR hi)).2.1)
    (range_of_permOK (permC_spec (pR hi)).1) h

private theorem badL {i : Nat} (hi : i < 30) :
    (badLetters i).size = 3 ∧ ∀ j < 3, (badLetters i)[j]! = unpack 1755 11 (PSb i j) := by
  refine ⟨by simp [badLetters], fun j hj => ?_⟩
  rw [badLetters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  split_ifs with h0 h1
  · dsimp only at h0
    subst h0
    rw [x_eq]
    rfl
  · dsimp only at h1
    subst h1
    rw [t_eq]
    rfl
  · dsimp only at h0 h1
    have e : j = 2 := by omega
    subst e
    rw [r_eq hi]
    rfl

private theorem badP {i : Nat} (hi : i < 30) :
    allN 3 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PSb i j) (PSIb i j)) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  interval_cases j
  · exact (permC_spec pX).1
  · exact (permC_spec pT).1
  · exact (permC_spec (pR hi)).1

private theorem bad_ok {i : Nat} (hi : i < 30) (h : badK i = true) : badOK i = true := by
  unfold badK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq] at h2
  obtain ⟨hc, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h12, h4⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨h13, h5⟩ := (bAnd_iff _ _).1 h4
  obtain ⟨e, hl⟩ := wordEqK_sound (badL hi) (badP hi) h1
  have ne : ∀ e, neId (pw (bw i) e) = true →
      eqA 1755 (powArr 1755 (badWordArr i) e) (idA 1755) = false := by
    intro e' he
    have hb : badWordArr i = unpack 1755 11 (bw i) := e
    rw [hb, (powU hc e').1, idA_eq', eqU (powU hc e').2 cId]
    unfold neId at he
    cases hq : Nat.beq (pw (bw i) e') (pidn 1755 11)
    · rfl
    · rw [hq] at he
      exact absurd he Bool.false_ne_true
  unfold badOK
  rw [hl, ne 12 h12, ne 13 h13, ne 5 h5]
  rfl

private theorem reps_ok : (allLt 30 fun i => if titsRepGood.getD i false then inTitsK0 (titsRepArr i) else
    badOK i) = true := by
  rw [allLt_iff]
  intro i hi
  have g := allN_spec good i hi
  have b := allN_spec bad i hi
  rw [bIf_eq] at g b
  split
  · rename_i hg
    simp only [hg, ↓reduceIte] at g
    exact good_sift hi g
  · rename_i hg
    simp only [hg] at b
    exact bad_ok hi b

private theorem titsCls_check_0 :
    isInvA 1755 titsAuxArr (invCand 1755 titsAuxArr) = true ∧ inTitsA titsAuxArr = true ∧
      inTitsD titsAuxArr = false ∧
      eqA 1755 (compA 1755 titsAuxArr titsTArr) (compA 1755 titsTArr titsAuxArr) = true ∧
      isInvA 1755 titsY12Arr (invCand 1755 titsY12Arr) = true ∧ inTitsA titsY12Arr = true ∧
      eqA 1755 (compA 1755 titsY12Arr titsTArr) (compA 1755 titsTArr titsY12Arr) = true ∧
      eqA 1755 (compA 1755 titsY12Arr titsX13Arr)
        (compA 1755 (powArr 1755 titsX13Arr 11) titsY12Arr) = true ∧
      (allLt 12 fun k => isInvA 1755 (powArr 1755 titsY12Arr k)
        (invCand 1755 (powArr 1755 titsY12Arr k))) = true ∧
      (titsCNt.all fun c => classOK c && classOK (compA 1755 titsAuxArr c)) = true ∧
      (allLt 30 fun i => isInvA 1755 (titsRepArr i) (invCand 1755 (titsRepArr i))) = true ∧
      titsRepGood.length = 30 ∧ titsBadWords.length = 30 ∧
      (allLt 30 fun i => if titsRepGood.getD i false then inTitsK0 (titsRepArr i) else
        badOK i) = true ∧
      ruChainOK 1755 titsK0Strong 3 5 [0, 12, 1] titsK0Words = true ∧
      rawOrbitSizes 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1]) = [975, 4, 2] ∧
      eqA 1755 titsK0Strong[0]! titsX13Arr = true ∧ eqA 1755 titsK0Strong[1]! titsTArr = true ∧
      inTitsA titsK0Strong[2]! = true ∧
      isInvA 1755 titsTArr (invCand 1755 titsTArr) = true ∧
      eqA 1755 (compA 1755 (compA 1755 (compA 1755 titsTArr titsX13Arr) titsTArr) titsX13Arr)
        (idA 1755) = true := by
  have cA := cOf pAux
  have cY := cOf pY
  have cX := cOf pX
  have cT := cOf pT
  have k0 := (bAnd_iff (Nat.beq (TK.F 0) X) (Nat.beq (TK.F 1) TitsT)).1 k0X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cnt_ok, ?_, rfl, rfl, reps_ok, k0_chain, k0_orbits,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [aux_eq]
    exact isInv_of pAux
  · rw [aux_eq]
    exact inA_of_a pAux auxA
  · rw [aux_eq]
    exact notD_of pAux auxD
  · rw [aux_eq, t_eq, cmp cA cT, cmp cT cA, eqU (cmpC cA cT) (cmpC cT cA)]
    exact auxT
  · rw [y_eq]
    exact isInv_of pY
  · rw [y_eq]
    exact inA_of_a pY yA
  · rw [y_eq, t_eq, cmp cY cT, cmp cT cY, eqU (cmpC cY cT) (cmpC cT cY)]
    exact yT
  · rw [y_eq, x_eq, (powU cX 11).1, cmp cY cX, cmp (powU cX 11).2 cY,
      eqU (cmpC cY cX) (cmpC (powU cX 11).2 cY)]
    exact yX
  · rw [allLt_iff]
    intro k hk
    obtain ⟨e1, -, e3⟩ := yl_spec hk
    rw [e1]
    exact isInv_of e3
  · rw [allLt_iff]
    intro i hi
    rw [r_eq hi]
    exact isInv_of (pR hi)
  · rw [k_eq (by norm_num), x_eq, Nat.eq_of_beq_eq_true k0.1, eqU cX cX, Nat.beq_refl]
  · rw [k_eq (by norm_num), t_eq, Nat.eq_of_beq_eq_true k0.2, eqU cT cT, Nat.beq_refl]
  · rw [k_eq (by norm_num)]
    exact inA_of_D (pK (by norm_num)) k2A
  · rw [t_eq]
    exact isInv_of pT
  · rw [t_eq, x_eq, cmp cT cX, cmp (cmpC cT cX) cT, cmp (cmpC (cmpC cT cX) cT) cX, idA_eq',
      eqU (cmpC (cmpC (cmpC cT cX) cT) cX) cId]
    exact tX

end CertificateChecks.Batch7050

namespace Certificates

open CertificateChecks

end Certificates

end
