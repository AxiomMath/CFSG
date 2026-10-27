module

public import Certificates.Kernel.CF23L34.SuzChecks
public import CFSG.Certificates.Kernel.CF23L34.WordSound
import CFSG.Certificates.Kernel.Item434GenSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.CF23Suz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CF23L34 CFSG.KC.BfsPin
open CFSG.ComponentClassification.GSThmB.CF23L34 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore CFSG.LieType.Multipliers.L34
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem szOK1782 : szOK 1782 11 = true := rfl

theorem gen_facts {i : Nat} (hi : i < 3) :
    PP 1782 11 (SuzFus.F i) ∧ pinvS 1782 11 (mask 11) (SuzFus.F i) = SuzFusI i ∧
      msift (SuzFus.F i) = true := by
  have h := allN_spec ch22223_gen i hi
  unfold genK at h
  simp only [bAnd_iff] at h
  obtain ⟨hinv, hperm, hin⟩ := h
  have e := Nat.eq_of_beq_eq_true hinv
  refine ⟨PP_of_permOK szOK1782 ?_, e, hin⟩
  rw [e]
  exact hperm

theorem genI_facts {i : Nat} (hi : i < 3) : PP 1782 11 (SuzFusI i) := by
  obtain ⟨hp, e, -⟩ := gen_facts hi
  rw [← e]
  exact hp.inv

theorem rest_facts :
    PP 1782 11 (SuzTP 0) ∧ commK 1782 11 (mask 11) (1782 * 11) (SuzFus.F 0) (SuzTP 0) = true ∧
      commK 1782 11 (mask 11) (1782 * 11) (SuzFus.F 1) (SuzTP 0) = true ∧
      Nat.beq (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (SuzFus.F 2) (SuzTP 0))
        (SuzFusI 2)) (pcomp 1782 11 (mask 11) (SuzTP 0) (SuzFus.F 0)) = true ∧
      Nat.beq (SuzFus.F 0) (pidn 1782 11) = false := by
  have h := ch22223_rest
  unfold restK at h
  simp only [bAnd_iff] at h
  obtain ⟨hT, h0, h1, hc, hn⟩ := h
  refine ⟨PP_of_permOK szOK1782 hT, h0, h1, hc, ?_⟩
  cases e : Nat.beq (SuzFus.F 0) (pidn 1782 11)
  · rfl
  · rw [e] at hn
    exact absurd hn (by decide)

theorem gens_get : ∀ i < 2, suzGens[i]! = unpack 1782 11 (SuzFus.F i) ∧ PP 1782 11 (SuzFus.F i) := by
  intro i hi
  interval_cases i
  · exact ⟨y1_eq, (gen_facts (by norm_num)).1⟩
  · exact ⟨y2_eq, (gen_facts (by norm_num)).1⟩

theorem gensInv_get :
    ∀ i < 2, suzGensInv[i]! = unpack 1782 11 (SuzFusI i) ∧ PP 1782 11 (SuzFusI i) := by
  intro i hi
  obtain ⟨hg, hp⟩ := gens_get i hi
  obtain ⟨-, e, -⟩ := gen_facts (i := i) (by omega)
  have hs : i < suzGens.size := by
    have : suzGens.size = 2 := rfl
    omega
  refine ⟨?_, genI_facts (by omega)⟩
  rw [suzGensInv, CFSG.KC.Item434Gen.map_getElem! _ _ hs, hg, invCand_PP hp, e]

theorem words_true : ∀ i < 23, wordK i = true := by
  intro i hi
  interval_cases i
  exacts [ch22223w_0, ch22223w_1, ch22223w_2, ch22223w_3, ch22223w_4, ch22223w_5, ch22223w_6,
    ch22223w_7, ch22223w_8, ch22223w_9, ch22223w_10, ch22223w_11, ch22223w_12, ch22223w_13,
    ch22223w_14, ch22223w_15, ch22223w_16, ch22223w_17, ch22223w_18, ch22223w_19, ch22223w_20,
    ch22223w_21, ch22223w_22]

theorem words_all : (coverWs ++ [zOne, zTwo, zThree]).all (fun w =>
    eqA 1782 (evalFW 1782 suzGens suzGensInv w) (idA 1782)) = true := by
  have hS := evalFW_sound szOK1782 gens_get gensInv_get
  have e : coverWs ++ [zOne, zTwo, zThree] = suzWs := rfl
  rw [e, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hw := words_true i (ch22223_len ▸ hi)
  unfold wordK suzEv at hw
  rw [List.getD_eq_getElem _ _ hi] at hw
  rw [(hS _).1]
  exact eq_id_sound szOK1782 (hS _).2 hw

theorem suzFusOK_true : suzFusOK = true := by
  obtain ⟨hP0, -, hin0⟩ := gen_facts (i := 0) (by norm_num)
  obtain ⟨hP1, -, hin1⟩ := gen_facts (i := 1) (by norm_num)
  obtain ⟨hP2, hi2, hin2⟩ := gen_facts (i := 2) (by norm_num)
  obtain ⟨hT, hc0, hc1, hcj, hne⟩ := rest_facts
  have ht : tArr 0 = unpack 1782 11 (SuzTP 0) := (rep_facts (i := 0) (by norm_num)).1
  have i0 : suzGensInv[0]! = invCand 1782 suzY1Arr := by
    rw [(gensInv_get 0 (by norm_num)).1, y1_eq, invCand_PP hP0, (gen_facts (i := 0) (by norm_num)).2.1]
  have i1 : suzGensInv[1]! = invCand 1782 suzY2Arr := by
    rw [(gensInv_get 1 (by norm_num)).1, y2_eq, invCand_PP hP1, (gen_facts (i := 1) (by norm_num)).2.1]
  have f1 : isInvA 1782 suzY1Arr suzGensInv[0]! = true := by
    rw [i0, y1_eq]
    exact CFSG.KC.Item434Gen.isInvA_PP szOK1782 hP0
  have f2 : isInvA 1782 suzY2Arr suzGensInv[1]! = true := by
    rw [i1, y2_eq]
    exact CFSG.KC.Item434Gen.isInvA_PP szOK1782 hP1
  have f3 : isInvA 1782 suzMArr (invCand 1782 suzMArr) = true := by
    rw [m_eq]
    exact CFSG.KC.Item434Gen.isInvA_PP szOK1782 hP2
  have f4 : inM suzY1Arr = true := by rw [inM_eq y1_eq hP0.1]; exact hin0
  have f5 : inM suzY2Arr = true := by rw [inM_eq y2_eq hP1.1]; exact hin1
  have f6 : inM suzMArr = true := by rw [inM_eq m_eq hP2.1]; exact hin2
  have f7 : commutesA suzY1Arr (tArr 0) = true := by
    rw [y1_eq, ht]
    exact commutes_eq hc0
  have f8 : commutesA suzY2Arr (tArr 0) = true := by
    rw [y2_eq, ht]
    exact commutes_eq hc1
  have f10 : eqA 1782 (compA 1782 (compA 1782 suzMArr (tArr 0)) (invCand 1782 suzMArr))
      (compA 1782 (tArr 0) suzY1Arr) = true := by
    rw [m_eq, ht, y1_eq]
    exact conj_sound hP2 hT hP0 hi2 hcj
  have f11 : (!eqA 1782 suzY1Arr (idA 1782)) = true := by
    rw [y1_eq]
    exact ne_id_sound szOK1782 hP0 hne
  unfold suzFusOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩, f8⟩, words_all⟩, f10⟩, f11⟩

end CertificateChecks.KernelLC.CF23Suz

end
