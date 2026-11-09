module

public import Certificates.Kernel.LocalComp.HeFixBind
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.RawCongr
public import Certificates.Kernel.Tc.HeW0
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Spor.PackFld
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public import CFSG.Certificates.Kernel.Spor.Loops
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo2Chain.He12635

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def arrsM : Array (Array Nat) :=
  ((List.range 4).map heThreeCA ++ (List.range 4).map heThreeCB).toArray

meta def invsM : Array (Array Nat) := arrsM.map (CFSG.Monster.B.Co2.Native.invCand 8330)

meta def arrsB : Array (Array Nat) :=
  let b := heThreeWordsB
  #[(b.getD 0 []).take 19, (b.getD 0 []).drop 19,
    (b.getD 1 []).take 22, ((b.getD 1 []).drop 22).take 22, (b.getD 1 []).drop 44,
    (b.getD 2 []).take 23, ((b.getD 2 []).drop 23).take 22, (b.getD 2 []).drop 45,
    (b.getD 3 []).take 24, ((b.getD 3 []).drop 24).take 23, (b.getD 3 []).drop 47].map heThreeArr

end CertificateChecks.KernelCo2Chain.He12635

public section

#kmisc_packarrs CertificateChecks.KernelCo2Chain.He12635.HT
  CertificateChecks.KernelCo2Chain.He12635.arrsM 14

#kmisc_packarrs CertificateChecks.KernelCo2Chain.He12635.HTI
  CertificateChecks.KernelCo2Chain.He12635.invsM 14

#kmisc_packarrs CertificateChecks.KernelCo2Chain.He12635.HB
  CertificateChecks.KernelCo2Chain.He12635.arrsB 14

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He12635

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CertificateChecks.KernelLC.HeFix

@[expose] noncomputable abbrev pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def tabR (o j : Nat) : Bool :=
  bAnd(Nat.blt (Nat.add o j) (nat_lit 8),
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (HT (o + j)) (HTI (o + j)),
  bAnd(invEqK 8330 14 (mask 14) (8330 * 14) (HTI (o + j)) (HT (o + j)),
  bAnd(cn (HT (o + j)), cn (HTI (o + j))))))

@[expose] noncomputable def restR (o cnt : Nat) (Δ : Array Nat) (m : Nat) : Bool :=
  bAnd(allN 4 (fun j => Nat.beq (pc (HT (o + j)) (HT o)) (pc (HT o) (HT (o + j)))),
  bAnd(Nat.beq (pc (HT o) (pc (HT o) (HT o))) (pidn 8330 14),
  bAnd(bIf(Nat.beq (HT o) (pidn 8330 14), false, true),
  bAnd(Nat.beq (pg 14 (mask 14) (HT o) 0) 0,
  bAnd(Nat.beq (CertificateChecks.KernelSpor.OddCore.fixCntK 8330 14 (mask 14) (HT o)) cnt,
    allLt m (fun k => Nat.blt (Δ[k]!) 8330))))))

@[expose] noncomputable def classR (o cnt : Nat) (Δ : Array Nat) (m : Nat) : Bool :=
  bAnd(allN 4 (fun j => tabR o j), restR o cnt Δ m)

@[expose] noncomputable def wK (W : List (List Int)) (o j : Nat) : Bool :=
  wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (W.getD j []) (HT (o + j))

@[expose] noncomputable def classK (W : List (List Int)) (o cnt : Nat) (Δ : Array Nat) (m : Nat) :
    Bool :=
  bAnd(allN 4 (fun j => bAnd(wK W o j, tabR o j)), restR o cnt Δ m)

theorem glueK {F G : Nat → Bool} {r : Bool} (hF : ∀ j < 4, F j = true)
    (hR : bAnd(allN 4 (fun j => G j), r) = true) :
    bAnd(allN 4 (fun j => bAnd(F j, G j)), r) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hR
  exact (bAnd_iff _ _).2 ⟨CFSG.KS.PackFld.allN_of_forall fun j hj =>
    (bAnd_iff _ _).2 ⟨hF j hj, CFSG.KS.allN_spec h1 j hj⟩, h2⟩

theorem classK_of {W : List (List Int)} {o cnt m : Nat} {Δ : Array Nat}
    (hW : ∀ j < 4, wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (W.getD j []) (HT (o + j)) =
      true)
    (hR : classR o cnt Δ m = true) : classK W o cnt Δ m = true := by
  unfold classR at hR
  unfold classK
  exact glueK (F := wK W o) (G := tabR o) (r := restR o cnt Δ m) hW hR

theorem kRA : classR 0 77 heThreeDeltaA 35 = true := by
  quickRfl

theorem kRB : classR 4 8 heThreeDeltaB 8 = true := by
  quickRfl

@[expose] def bcs : List (List Int) :=
  let b := heThreeWordsB
  [(b.getD 0 []).take 19, (b.getD 0 []).drop 19,
    (b.getD 1 []).take 22, ((b.getD 1 []).drop 22).take 22, (b.getD 1 []).drop 44,
    (b.getD 2 []).take 23, ((b.getD 2 []).drop 23).take 22, (b.getD 2 []).drop 45,
    (b.getD 3 []).take 24, ((b.getD 3 []).drop 24).take 23, (b.getD 3 []).drop 47]

@[expose] noncomputable def bOK (k : Nat) : Bool :=
  Nat.beq (CertificateChecks.KernelTc.He.wordC (bcs.getD k [])) (HB k)

#kc_each CertificateChecks.KernelCo2Chain.He12635.bOK 0 11

theorem kW : bAnd(Nat.beq (CertificateChecks.KernelTc.He.HWQ 4) (HT 0),
    bAnd(Nat.beq (CertificateChecks.KernelTc.He.HWX 0) (HT 1),
    bAnd(Nat.beq (CertificateChecks.KernelTc.He.HWX 1) (HT 2),
    bAnd(Nat.beq (CertificateChecks.KernelTc.He.HT 6) (HT 3),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HB 0) (HB 1)) (HT 4),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HB 2) (pcompC 8330 14 (mask 14) (HB 3) (HB 4))) (HT 5),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HB 5) (pcompC 8330 14 (mask 14) (HB 6) (HB 7))) (HT 6),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HB 8) (pcompC 8330 14 (mask 14) (HB 9) (HB 10))) (HT 7),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HB 1),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HB 4),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HB 7),
      canonK 8330 14 (mask 14) (8330 * 14) (HB 10)))))))))))) = true := by
  quickRfl

theorem eB (k : Nat) (h : bOK k = true) :
    wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (bcs.getD k []) = HB k := by
  unfold bOK at h
  rw [CertificateChecks.KernelTc.He.wordC_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem eB3 {j a b c : Nat} (e : heThreeWordsB.getD j [] = bcs.getD a [] ++ (bcs.getD b [] ++ bcs.getD c []))
    (ha : bOK a = true) (hb : bOK b = true) (hc : bOK c = true)
    (cc : canonK 8330 14 (mask 14) (8330 * 14) (HB c) = true) :
    wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heThreeWordsB.getD j []) =
      pcomp 8330 14 (mask 14) (HB a) (pcomp 8330 14 (mask 14) (HB b) (HB c)) := by
  have h := CertificateChecks.KernelTc.He.appK (eB b hb) (eB c hc) cc
  rw [e, (CertificateChecks.KernelTc.He.appK (eB a ha) h.1 h.2).1]

theorem wordEq_of {wd : List Int} {r : Nat}
    (e : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I wd = r)
    (hl : bAnd(szOK 8330 14, lettersK 2 wd) = true) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 wd r = true := by
  unfold wordEqK
  rw [e, Nat.beq_refl]
  simp only [bAnd_iff] at hl ⊢
  exact ⟨hl.1, hl.2, trivial⟩

theorem kL : allN 4 (fun j => bAnd(bAnd(szOK 8330 14, lettersK 2 (heThreeWordsA.getD j [])),
    bAnd(szOK 8330 14, lettersK 2 (heThreeWordsB.getD j [])))) = true := by
  quickRfl

theorem wA : ∀ j < 4, wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (heThreeWordsA.getD j [])
    (HT (0 + j)) = true := by
  have hc := kW
  simp only [bAnd_iff] at hc
  obtain ⟨h0, h1, h2, h3, -⟩ := hc
  intro j hj
  have hl := ((bAnd_iff _ _).1 (allN_spec kL j hj)).1
  match j, hj, hl with
  | 0, _, hl =>
    have e : heThreeWordsA.getD 0 [] = CertificateChecks.KernelTc.He.heTcWs.getD 14 [] := rfl
    rw [e] at hl ⊢
    exact wordEq_of (CertificateChecks.KernelTc.He.eA0.trans (Nat.eq_of_beq_eq_true h0)) hl
  | 1, _, hl =>
    have e : heThreeWordsA.getD 1 [] = CertificateChecks.KernelTc.He.wX.getD 0 [] := rfl
    rw [e] at hl ⊢
    exact wordEq_of (CertificateChecks.KernelTc.He.eX0.trans (Nat.eq_of_beq_eq_true h1)) hl
  | 2, _, hl =>
    have e : heThreeWordsA.getD 2 [] = CertificateChecks.KernelTc.He.wX.getD 1 [] := rfl
    rw [e] at hl ⊢
    exact wordEq_of (CertificateChecks.KernelTc.He.eX1.trans (Nat.eq_of_beq_eq_true h2)) hl
  | 3, _, hl =>
    have e : heThreeWordsA.getD 3 [] = CertificateChecks.KernelTc.He.heTcWs.getD 6 [] := rfl
    rw [e] at hl ⊢
    exact wordEq_of (CertificateChecks.KernelTc.He.eR1.trans (Nat.eq_of_beq_eq_true h3)) hl
  | _ + 4, h, _ => exact absurd h (by omega)

theorem wB : ∀ j < 4, wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (heThreeWordsB.getD j [])
    (HT (4 + j)) = true := by
  have hc := kW
  simp only [bAnd_iff, CFSG.KS.PK.pcompC_eq] at hc
  obtain ⟨-, -, -, -, h4, h5, h6, h7, c1, c4, c7, c10⟩ := hc
  intro j hj
  have hl := ((bAnd_iff _ _).1 (allN_spec kL j hj)).2
  match j, hj, hl with
  | 0, _, hl =>
    have e : heThreeWordsB.getD 0 [] = bcs.getD 0 [] ++ bcs.getD 1 [] := rfl
    have h := CertificateChecks.KernelTc.He.appK (eB 0 bOK0) (eB 1 bOK1) c1
    refine wordEq_of ?_ hl
    rw [e, h.1]
    exact Nat.eq_of_beq_eq_true h4
  | 1, _, hl => exact wordEq_of ((eB3 (j := 1) (a := 2) (b := 3) (c := 4) rfl bOK2 bOK3 bOK4 c4).trans
      (Nat.eq_of_beq_eq_true h5)) hl
  | 2, _, hl => exact wordEq_of ((eB3 (j := 2) (a := 5) (b := 6) (c := 7) rfl bOK5 bOK6 bOK7 c7).trans
      (Nat.eq_of_beq_eq_true h6)) hl
  | 3, _, hl => exact wordEq_of ((eB3 (j := 3) (a := 8) (b := 9) (c := 10) rfl bOK8 bOK9 bOK10
      c10).trans (Nat.eq_of_beq_eq_true h7)) hl
  | _ + 4, h, _ => exact absurd h (by omega)

theorem kA : classK heThreeWordsA 0 77 heThreeDeltaA 35 = true := classK_of wA kRA

theorem kB : classK heThreeWordsB 4 8 heThreeDeltaB 8 = true := classK_of wB kRB

theorem kAgreeA : (allLt 4 fun j => (allLt 35 fun k =>
    pg 14 (mask 14) (HT (0 + j)) heThreeDeltaA[k]! ==
      heThreeDeltaA[(heThreeSigmaA.getD j #[])[k]!]!)) = true := by
  quickRfl

theorem kAgreeB : (allLt 4 fun j => (allLt 8 fun k =>
    pg 14 (mask 14) (HT (4 + j)) heThreeDeltaB[k]! ==
      heThreeDeltaB[(heThreeSigmaB.getD j #[])[k]!]!)) = true := by
  quickRfl

theorem kFixA : (allLt 35 fun k => pg 14 (mask 14) (HT 0) heThreeDeltaA[k]! == heThreeDeltaA[k]!) =
    true := by
  quickRfl

theorem kFixB : (allLt 8 fun k => pg 14 (mask 14) (HT 4) heThreeDeltaB[k]! == heThreeDeltaB[k]!) =
    true := by
  quickRfl

theorem allLt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i.1 i.2

theorem hS : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (L2 j) := by
  refine ⟨by simp [heABArrs], fun j hj => ?_⟩
  rw [heABArrs, arr_get _ (by simpa using hj)]
  match j, hj with
  | 0, _ => simpa [L2_0] using heGen_eq (k := 0) (by decide)
  | 1, _ => simpa [L2_1] using heGen_eq (k := 1) (by decide)

theorem countP_unpack (P : Nat) : (List.range 8330).countP (fun i => (unpack 8330 14 P)[i]! == i) =
    CertificateChecks.KernelSpor.OddCore.fixCntK 8330 14 (mask 14) P := by
  rw [CertificateChecks.KernelSpor.OddCore.fixCntK_eq]
  apply List.countP_congr
  intro i hi
  rw [unpack_get' (List.mem_range.1 hi)]
  cases h : Nat.beq (pg 14 (mask 14) P i) i
  · have : pg 14 (mask 14) P i ≠ i := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem permChk_unpack {P PI : Nat} (h1 : invEqK 8330 14 (mask 14) (8330 * 14) P PI = true)
    (h2 : invEqK 8330 14 (mask 14) (8330 * 14) PI P = true) :
    permChk 8330 (unpack 8330 14 P) = true := by
  obtain ⟨e1, i1⟩ := invEqK_sound h1
  obtain ⟨-, i2⟩ := invEqK_sound h2
  unfold permChk
  rw [e1, i1, i2]
  rfl

theorem class_facts {W : List (List Int)} {o cnt m : Nat} {Δ : Array Nat} {Sg : List (Array Nat)}
    (hk : classK W o cnt Δ m = true)
    (hag : (allLt 4 fun j => (allLt m fun k =>
      pg 14 (mask 14) (HT (o + j)) Δ[k]! == Δ[(Sg.getD j #[])[k]!]!)) = true)
    (hfx : (allLt m fun k => pg 14 (mask 14) (HT o) Δ[k]! == Δ[k]!) = true) :
    (permChk 8330 (heThreeArr (W.getD 0 [])) = true ∧
      eqA 8330 (compA 8330 (heThreeArr (W.getD 0 []))
        (compA 8330 (heThreeArr (W.getD 0 [])) (heThreeArr (W.getD 0 [])))) (idA 8330) = true ∧
      eqA 8330 (heThreeArr (W.getD 0 [])) (idA 8330) = false ∧ (heThreeArr (W.getD 0 []))[0]! = 0 ∧
      (List.range 8330).countP (fun i => (heThreeArr (W.getD 0 []))[i]! == i) = cnt) ∧
    (∀ j < 4, permChk 8330 (heThreeArr (W.getD j [])) = true ∧
      eqA 8330 (compA 8330 (heThreeArr (W.getD j [])) (heThreeArr (W.getD 0 [])))
        (compA 8330 (heThreeArr (W.getD 0 [])) (heThreeArr (W.getD j []))) = true ∧
      agreeOK m (heThreeArr (W.getD j [])) Δ (Sg.getD j #[]) = true) ∧
    fixesOK m (heThreeArr (W.getD 0 [])) Δ = true ∧
    eqA 8330 (heThreeArr (W.getD 0 [])) (heThreeArr (W.getD 0 [])) = true := by
  unfold classK restR at hk
  simp only [bAnd_iff] at hk
  obtain ⟨hw, hcm, hcube, hne, h0, hcnt, hΔ⟩ := hk
  have hw' : ∀ j < 4, heThreeArr (W.getD j []) = unpack 8330 14 (HT (o + j)) ∧
      permChk 8330 (heThreeArr (W.getD j [])) = true ∧ cn (HT (o + j)) = true := by
    intro j hj
    have h := CFSG.KS.allN_spec hw j hj
    simp only [bAnd_iff, tabR, wK] at h
    obtain ⟨h1, -, h2, h3, h4, -⟩ := h
    have e : heThreeArr (W.getD j []) = unpack 8330 14 (HT (o + j)) :=
      (wordEqK_sound hS kPL2 h1).1
    exact ⟨e, by rw [e]; exact permChk_unpack h2 h3, h4⟩
  obtain ⟨eB, pB, cB⟩ := hw' 0 (by decide)
  rw [Nat.add_zero] at eB cB
  have hΔ' : ∀ k < m, Δ[k]! < 8330 := fun k hk =>
    Nat.le_of_ble_eq_true (allLt_iff.1 hΔ k hk)
  have hidA' := hidA
  refine ⟨⟨pB, ?_, ?_, ?_, ?_⟩, fun j hj => ?_, ?_, ?_⟩
  · rw [eB, compA_unpack cB cB, compA_unpack cB (canonK_pcomp cB cB), hidA',
      eqA_unpack (canonK_pcomp cB (canonK_pcomp cB cB)) hid]
    exact hcube
  · rw [eB, hidA', eqA_unpack cB hid]
    cases h : Nat.beq (HT o) (pidn 8330 14)
    · rfl
    · rw [h] at hne
      exact absurd hne (by decide)
  · rw [eB, unpack_get' (by decide)]
    exact Nat.eq_of_beq_eq_true h0
  · rw [eB, countP_unpack]
    exact Nat.eq_of_beq_eq_true hcnt
  · obtain ⟨eC, pC, cC⟩ := hw' j hj
    refine ⟨pC, ?_, ?_⟩
    · rw [eC, eB, compA_unpack cC cB, compA_unpack cB cC,
        eqA_unpack (canonK_pcomp cC cB) (canonK_pcomp cB cC)]
      exact CFSG.KS.allN_spec hcm j hj
    · have h := allLt_iff.1 hag j hj
      unfold agreeOK
      rw [eC, ← h]
      refine CFSG.KS.Raw.allLt_congr fun k hk => ?_
      rw [unpack_get' (hΔ' k hk)]
  · unfold fixesOK
    rw [eB, ← hfx]
    refine CFSG.KS.Raw.allLt_congr fun k hk => ?_
    rw [unpack_get' (hΔ' k hk)]
  · rw [eB, eqA_unpack cB cB, Nat.beq_refl]

theorem facts :
    ((lettersOK 2 (heThreeWordsA.getD 0 []) = true ∧ permChk 8330 heThreeBA = true ∧
        eqA 8330 (compA 8330 heThreeBA (compA 8330 heThreeBA heThreeBA)) (idA 8330) = true ∧
        eqA 8330 heThreeBA (idA 8330) = false ∧ heThreeBA[0]! = 0 ∧
        (List.range 8330).countP (fun i => heThreeBA[i]! == i) = 77) ∧
      (heThreeWordsA.length = 4 ∧
        ∀ j < 4, lettersOK 2 (heThreeWordsA.getD j []) = true ∧ permChk 8330 (heThreeCA j) = true ∧
          eqA 8330 (compA 8330 (heThreeCA j) heThreeBA) (compA 8330 heThreeBA (heThreeCA j)) = true ∧
          permChk 35 (heThreeSigmaA.getD j #[]) = true ∧
          agreeOK 35 (heThreeCA j) heThreeDeltaA (heThreeSigmaA.getD j #[]) = true) ∧
      (incListOK 8330 35 heThreeDeltaA = true ∧ fixesOK 35 heThreeBA heThreeDeltaA = true ∧
        eqA 8330 (heThreeCA 0) heThreeBA = true))
    ∧ ((lettersOK 2 (heThreeWordsB.getD 0 []) = true ∧ permChk 8330 heThreeBB = true ∧
        eqA 8330 (compA 8330 heThreeBB (compA 8330 heThreeBB heThreeBB)) (idA 8330) = true ∧
        eqA 8330 heThreeBB (idA 8330) = false ∧ heThreeBB[0]! = 0 ∧
        (List.range 8330).countP (fun i => heThreeBB[i]! == i) = 8) ∧
      (heThreeWordsB.length = 4 ∧
        ∀ j < 4, lettersOK 2 (heThreeWordsB.getD j []) = true ∧ permChk 8330 (heThreeCB j) = true ∧
          eqA 8330 (compA 8330 (heThreeCB j) heThreeBB) (compA 8330 heThreeBB (heThreeCB j)) = true ∧
          permChk 8 (heThreeSigmaB.getD j #[]) = true ∧
          agreeOK 8 (heThreeCB j) heThreeDeltaB (heThreeSigmaB.getD j #[]) = true) ∧
      (incListOK 8330 8 heThreeDeltaB = true ∧ fixesOK 8 heThreeBB heThreeDeltaB = true ∧
        eqA 8330 (heThreeCB 0) heThreeBB = true)) := by
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, a6, a7, a8⟩ := class_facts (Sg := heThreeSigmaA) kA kAgreeA kFixA
  obtain ⟨⟨b1, b2, b3, b4, b5⟩, b6, b7, b8⟩ := class_facts (Sg := heThreeSigmaB) kB kAgreeB kFixB
  have lA : ∀ j < 4, lettersOK 2 (heThreeWordsA.getD j []) = true := by decide
  have lB : ∀ j < 4, lettersOK 2 (heThreeWordsB.getD j []) = true := by decide
  have sA : ∀ j < 4, permChk 35 (heThreeSigmaA.getD j #[]) = true := by decide +kernel
  have sB : ∀ j < 4, permChk 8 (heThreeSigmaB.getD j #[]) = true := by decide +kernel
  have iA : incListOK 8330 35 heThreeDeltaA = true := by decide +kernel
  have iB : incListOK 8330 8 heThreeDeltaB = true := by decide +kernel
  refine ⟨⟨⟨lA 0 (by decide), a1, a2, a3, a4, a5⟩, ⟨by decide, fun j hj => ?_⟩, iA, a7, a8⟩,
    ⟨⟨lB 0 (by decide), b1, b2, b3, b4, b5⟩, ⟨by decide, fun j hj => ?_⟩, iB, b7, b8⟩⟩
  · obtain ⟨p, c, g⟩ := a6 j hj
    exact ⟨lA j hj, p, c, sA j hj, g⟩
  · obtain ⟨p, c, g⟩ := b6 j hj
    exact ⟨lB j hj, p, c, sB j hj, g⟩

end CertificateChecks.KernelCo2Chain.He12635

end
