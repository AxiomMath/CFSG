module

public import Certificates.Kernel.D4QK.Bind
public import Certificates.Kernel.S63K.I21111
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSegSound
public import CFSG.Certificates.Kernel.D4QK.TabSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelD4Q

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KC.D4QK CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert
open CFSG.KC.Co1B (mulWK)
open CFSG.KS.SporSch.M24 (gtPinK gtPinK_of_seg)
open CertificateChecks.KernelS63

theorem eltsP :
    eqM Y1 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 0 [])) = true ∧
    eqM Y2 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 1 [])) = true ∧
    eqM ZE (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 2 [])) = true ∧
    eqM R0 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 3 [])) = true ∧
    eqM S0 (wordK ID.G CFSG.KS.SporSch.M24.idM (nWords.getD 4 [])) = true ∧
    Nat.beq oneK CFSG.KS.SporSch.M24.idM = true ∧
    Nat.beq (GK 0) ZE = true ∧ Nat.beq (GK 1) R0 = true ∧ Nat.beq (GK 2) S0 = true ∧
    Nat.beq (GZ 0) ZE = true := by
  have h := elts
  unfold eltsK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem hone : oneK = idP := by rw [Nat.eq_of_beq_eq_true eltsP.2.2.2.2.2.1, idM_eq]

theorem nW (i : Nat) (hi : i < 5) : wA i = unpackR 24 (wordK ID.G CFSG.KS.SporSch.M24.idM
    (nWords.getD i [])) := by
  unfold wA
  apply I21111.word_eq
  interval_cases i <;> decide

theorem hy1 : y1A = unpackR 24 Y1 := by rw [y1A, nW 0 (by norm_num), ← eqM_iff.1 eltsP.1]

theorem hy2 : y2A = unpackR 24 Y2 := by rw [y2A, nW 1 (by norm_num), ← eqM_iff.1 eltsP.2.1]

theorem hz : zA = unpackR 24 ZE := by rw [zA, nW 2 (by norm_num), ← eqM_iff.1 eltsP.2.2.1]

theorem hr0 : r0A = unpackR 24 R0 := by rw [r0A, nW 3 (by norm_num), ← eqM_iff.1 eltsP.2.2.2.1]

theorem hs0 : s0A = unpackR 24 S0 := by rw [s0A, nW 4 (by norm_num), ← eqM_iff.1 eltsP.2.2.2.2.1]

theorem hy1i : y1iA = unpackR 24 Y1I := by rw [y1iA, hy1, powRows_eqK hone]; rfl

theorem hs0i : s0iA = unpackR 24 S0I := by rw [s0iA, hs0, mulWK_eq]; rfl

theorem zpowP : (∀ i < 7, eqM (ZP i) (powK ZE i) = true) ∧ eqM (powK ZE 7) oneK = true := by
  have h := zpow
  unfold zpowK at h
  rw [bAnd_eq', Bool.and_eq_true, allN_iff'] at h
  exact h

theorem zP : ∀ i < 7, unpackR 24 (ZP i) = unpackR 24 (powK ZE i) :=
  fun i hi => eqM_iff.1 (zpowP.1 i hi)

theorem z7 : unpackR 24 (powK ZE 7) = unpackR 24 oneK := eqM_iff.1 zpowP.2

theorem phi_eq (U V : Nat) : phiArr (unpackR 24 U) (unpackR 24 V) =
    Array.ofFn (n := 14) fun j => unpackR 24 (phK ZP U V j.val) := phiArr_eq hone hz zP z7 U V

theorem ofFn14_get (G : Nat → Nat) {l : Nat} (hl : l < 14) :
    (Array.ofFn (n := 14) fun j => unpackR 24 (G j.val))[l]! = unpackR 24 (G l) := ofFn_get G hl

theorem hq : ∀ l < 14, qGensA[l]! = unpackR 24 (GQ l) := fun l hl => by
  rw [qGensA, hy1, hy2, phi_eq, ofFn14_get _ hl]
  exact (eqM_iff.1 (allN_iff'.1 gq l hl)).symm

theorem hqA : qGensA = Array.ofFn (n := 14) fun l => unpackR 24 (GQ l.val) := by
  rw [qGensA, hy1, hy2, phi_eq]
  refine congrArg (fun f => Array.ofFn (n := 14) f) (funext fun l => ?_)
  exact (eqM_iff.1 (allN_iff'.1 gq l.val l.isLt)).symm

theorem hqi : ∀ l < 14, mulR qGensA[l]! qGensInvA[l]! = oneR := fun l hl => by
  rw [hq l hl, qGensInvA, hy1i, hy2, phi_eq, ofFn14_get _ hl, mulWK_eq, oneR_eqK hone]
  exact eqM_iff.1 (allN_iff'.1 gqi l hl)

theorem hqiv : ∀ l < 14, ∃ GI, qGensInvA[l]! = unpackR 24 GI := fun l hl =>
  ⟨_, by rw [qGensInvA, hy1i, hy2, phi_eq, ofFn14_get _ hl]⟩

theorem hs : ∀ l < 14, sGensA[l]! = unpackR 24 (GS l) := fun l hl => by
  have e1 : cmA y1A y1iA = unpackR 24 C1 := by
    rw [cmA, hy1, hy1i, hs0, hs0i, mulWK_eq, mulWK_eq, mulWK_eq]
    rfl
  have e2 : cmA y2A y2A = unpackR 24 C2 := by
    rw [cmA, hy2, hs0, hs0i, mulWK_eq, mulWK_eq, mulWK_eq]
    rfl
  rw [sGensA, e1, e2, phi_eq, ofFn14_get _ hl]
  exact (eqM_iff.1 (allN_iff'.1 gs l hl)).symm

theorem hsiv : ∀ l < 14, sGensInvA[l]! = unpackR 24 (phK ZP C1I C2I l) := fun l hl => by
  have e1 : cmiA y1A y1iA = unpackR 24 C1I := by
    rw [cmiA, hy1, hy1i, hs0, hs0i, mulWK_eq, mulWK_eq, mulWK_eq]
    rfl
  have e2 : cmiA y2A y2A = unpackR 24 C2I := by
    rw [cmiA, hy2, hs0, hs0i, mulWK_eq, mulWK_eq, mulWK_eq]
    rfl
  rw [sGensInvA, e1, e2, phi_eq, ofFn14_get _ hl]

theorem hsi : ∀ l < 14, mulR sGensA[l]! sGensInvA[l]! = oneR := fun l hl => by
  rw [hs l hl, hsiv l hl, mulWK_eq, oneR_eqK hone]
  exact eqM_iff.1 (allN_iff'.1 gsi l hl)

theorem invsP : eqM (mulWK ZE (ZP 6)) oneK = true ∧ eqM (mulWK R0 R0) oneK = true ∧
    eqM (mulWK S0 S0I) oneK = true ∧ eqM (mulWK Y1 Y1I) oneK = true ∧
    eqM (mulWK Y2 Y2) oneK = true := by
  have h := invs
  unfold invsK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem hz6 : zPowA[6]! = unpackR 24 (ZP 6) := by
  rw [zPowA_get hone hz (by norm_num), zP 6 (by norm_num)]

theorem gk0 : GK 0 = ZE := Nat.eq_of_beq_eq_true eltsP.2.2.2.2.2.2.1

theorem gk1 : GK 1 = R0 := Nat.eq_of_beq_eq_true eltsP.2.2.2.2.2.2.2.1

theorem gk2 : GK 2 = S0 := Nat.eq_of_beq_eq_true eltsP.2.2.2.2.2.2.2.2.1

theorem hk : ∀ l < 3, kGens[l]! = unpackR 24 (GK l) := fun l hl => by
  interval_cases l
  · rw [gk0, ← hz]; rfl
  · rw [gk1, ← hr0]; rfl
  · rw [gk2, ← hs0]; rfl

theorem hkiv : ∀ l < 3, ∃ GI, kGensInv[l]! = unpackR 24 GI := fun l hl => by
  interval_cases l
  · exact ⟨ZP 6, hz6⟩
  · exact ⟨R0, hr0⟩
  · exact ⟨S0I, hs0i⟩

theorem hki : ∀ l < 3, mulR kGens[l]! kGensInv[l]! = oneR := fun l hl => by
  rw [hk l hl, oneR_eqK hone]
  interval_cases l
  · change mulR _ zPowA[6]! = _
    rw [hz6, gk0, mulWK_eq]
    exact eqM_iff.1 invsP.1
  · change mulR _ r0A = _
    rw [hr0, gk1, mulWK_eq]
    exact eqM_iff.1 invsP.2.1
  · change mulR _ s0iA = _
    rw [hs0i, gk2, mulWK_eq]
    exact eqM_iff.1 invsP.2.2.1

theorem hb : ∀ l < 4, bGens[l]! = unpackR 24 (GB l) := fun l hl => by
  interval_cases l
  · exact hy1
  · exact hy2
  · exact hz
  · exact hr0

theorem lit4 (a b c d : Array ℕ) : (#[a, b, c, d] : Array (Array ℕ))[0]! = a ∧
    (#[a, b, c, d] : Array (Array ℕ))[1]! = b ∧ (#[a, b, c, d] : Array (Array ℕ))[2]! = c ∧
    (#[a, b, c, d] : Array (Array ℕ))[3]! = d := ⟨rfl, rfl, rfl, rfl⟩

theorem bInv0 : bGensInv[0]! = y1iA := by rw [bGensInv]; exact (lit4 _ _ _ _).1

theorem bInv1 : bGensInv[1]! = y2A := by rw [bGensInv]; exact (lit4 _ _ _ _).2.1

theorem bInv2 : bGensInv[2]! = zPowA[6]! := by rw [bGensInv]; exact (lit4 _ _ _ _).2.2.1

theorem bInv3 : bGensInv[3]! = r0A := by rw [bGensInv]; exact (lit4 _ _ _ _).2.2.2

theorem hbiv : ∀ l < 4, ∃ GI, bGensInv[l]! = unpackR 24 GI := fun l hl => by
  interval_cases l
  · exact ⟨Y1I, by rw [bInv0, hy1i]⟩
  · exact ⟨Y2, by rw [bInv1, hy2]⟩
  · exact ⟨ZP 6, by rw [bInv2, hz6]⟩
  · exact ⟨R0, by rw [bInv3, hr0]⟩

theorem hbi : ∀ l < 4, mulR bGens[l]! bGensInv[l]! = oneR := fun l hl => by
  rw [hb l hl, oneR_eqK hone]
  interval_cases l
  · rw [bInv0, hy1i, mulWK_eq]
    exact eqM_iff.1 invsP.2.2.2.1
  · rw [bInv1, hy2, mulWK_eq]
    exact eqM_iff.1 invsP.2.2.2.2
  · rw [bInv2, hz6, mulWK_eq]
    exact eqM_iff.1 invsP.1
  · rw [bInv3, hr0, mulWK_eq]
    exact eqM_iff.1 invsP.2.1

theorem qPin : gtPinK GQ 14 2049 QT.N QT.P QT.PAR QT.LAB QT.W QT.S = true :=
  gtPinK_of_seg qHead qSegs

theorem kPin : gtPinK GK 3 43 KT.N KT.P KT.PAR KT.LAB KT.W KT.S = true :=
  gtPinK_of_seg kHead fun i hi => by
    obtain rfl : i = 0 := by omega
    exact kSeg

theorem bPin : gtPinK GB 4 28673 BT.N BT.P BT.PAR BT.LAB BT.W BT.S = true :=
  gtPinK_of_seg bHead bSegs

theorem sPin : gtPinK GS 14 2049 ST.N ST.P ST.PAR ST.LAB ST.W ST.S = true :=
  gtPinK_of_seg sHead sSegs

theorem root_of {GM P PAR LAB W S : Nat → Nat} {ng cap N : Nat}
    (h : gtPinK GM ng cap N P PAR LAB W S = true) : unpackR 24 (P 0) = oneR := by
  rw [(pin_parts h).2.1, idM_eq, oneR_eq]

theorem tQ_eq : tQ = ElG QT.P 2048 := by
  have h := plK_sound _ _ plQ
  rw [tQ, h.2]
  exact buildTabR_eq (root_of qPin) (by simp [qGensA, phiArr]) hq (pin_tree qPin) (by decide)

theorem tK_eq : tK = ElG KT.P 42 := by
  have h := plK_sound _ _ plKc
  rw [tK, h.2]
  exact buildTabR_eq (root_of kPin) (by simp [kGens]) hk (pin_tree kPin) (by decide)

end CertificateChecks.KernelD4Q

end
