module

public import Certificates.Kernel.Co2Smith.Psi
public import Certificates.Kernel.Co2Smith.LabK
public import CFSG.Certificates.Kernel.Co2R3KSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Smith.GlCosetInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co2R3 CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Rank3.Native CFSG.Sporadic.Co2Smith.Native
open CertificateChecks.KernelSpor

theorem wordA_co2 {wd : List Int} (hl : CFSG.Monster.B.Co2.Native.lettersOK 11 wd = true) :
    CFSG.Monster.B.Co2.Native.wordA 2300 co2StrongArrs
      (CFSG.Certificates.Native.rawInvs 2300 co2StrongArrs) wd =
      unpack 2300 12 (wordK 2300 12 (mask 12) (pidn 2300 12) Co2A.S Co2A.SI wd) := by
  have hp := strong_permB
  refine CFSG.KC.Misc.ArrEnum.wordA_unpack sz_ok (j := 11) (fun h hh => Co2A.binds.2.2.2.2.1 h hh)
    (fun h hh => ?_) (fun h hh => ?_) (fun h hh => ?_) hl
  · rw [Orb.rawInvs_get (by rw [strong_size]; exact hh), Co2A.binds.2.2.2.2.1 h hh]
    exact CFSG.KC.LQT.Cov.T.invCand_unpack (allN_spec Co2A.perm h hh)
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have := allN_spec hp h hh
    simp only [Bool.and_eq_true] at this
    exact this.2

theorem lev1Gens_get {k : Nat} (hk : k < 10) : lev1Gens[k]! = unpack 2300 12 (G0 k) := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by
    omega
  have e : lev1Gens[k]! = co2StrongArrs[level1Idx.getD k 0]! := by
    unfold lev1Gens
    rw [getElem!_pos _ k (by simpa [level1Idx] using hk)]
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [e, G0]
  exact Co2A.binds.2.2.2.2.1 _ (by
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem lev2Gens_get {k : Nat} (hk : k < 8) : lev2Gens[k]! = unpack 2300 12 (G2 k) := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  have e : lev2Gens[k]! = co2StrongArrs[level2Idx.getD k 0]! := by
    unfold lev2Gens
    rw [getElem!_pos _ k (by simpa [level2Idx] using hk)]
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [e, G2]
  exact Co2A.binds.2.2.2.2.1 _ (by
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem stabGens_get {k : Nat} (hk : k < 3) : stabGens[k]! = unpack 2300 12 (WS k) := by
  have h := ws_ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hl⟩, hw⟩ := h
  have hk' : k < (stabWords ()).length := by rw [hlen]; exact hk
  have e : stabGens[k]! = CFSG.Monster.B.Co2.Native.wordA 2300 co2StrongArrs
      (CFSG.Certificates.Native.rawInvs 2300 co2StrongArrs) (stabWords ())[k] := by
    unfold stabGens
    rw [getElem!_pos _ k (by simpa using hk')]
    simp
  have hd : (stabWords ()).getD k [] = (stabWords ())[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  have hw' := Nat.eq_of_beq_eq_true (allN_spec hw k hk)
  rw [hd] at hw'
  rw [e, wordA_co2 (hl _ (List.getElem_mem hk')), hw']

theorem p0Rec_eq : p0Rec = (unpack 2300 12 (LR 0), unpack 2300 12 (LR 1), unpack 2300 12 (LR 2),
    unpack 2300 12 (LR 3)) :=
  orbReplay_sound (by norm_num) (by simp [lev1Gens, level1Idx]) (fun k hk => lev1Gens_get hk)
    replay0

theorem stabRec_eq : stabRec = (unpack 2300 12 (LR 6), unpack 2300 12 (LR 7),
    unpack 2300 12 (LR 8), unpack 2300 12 (LR 9)) := by
  have hlen : (stabWords ()).length = 3 := by
    have h := ws_ok
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  exact orbReplay_sound (by norm_num) (by simp [stabGens, hlen]) (fun k hk => stabGens_get hk)
    replay1

theorem p01Rec_eq : p01Rec = (unpack 2300 12 (LR 12), unpack 2300 12 (LR 13),
    unpack 2300 12 (LR 14), unpack 2300 12 (LR 15)) :=
  orbReplay_sound (by norm_num) (by simp [lev2Gens, level2Idx]) (fun k hk => lev2Gens_get hk)
    replay2

theorem get12 {A x : Nat} (hx : x < 2300) : (unpack 2300 12 A)[x]! = at12 A x := by
  rw [CFSG.KS.Raw.Orb.unpack_get hx]
  rfl

theorem cosetLab_ok : glCosetLabOK = true := by
  have h := lab_ok
  have hc : CK = cP := rfl
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2, h3⟩, l1⟩, l2⟩, l3⟩, l4⟩, l5⟩, l6⟩ := h
  unfold glCosetLabOK
  rw [stabRec_eq, p01Rec_eq, p0Rec_eq, cArr_eq, hc]
  dsimp only
  rw [get12 (A := cP) (x := 578) (by norm_num), get12 (A := cP) (x := 3) (by norm_num),
    get12 (A := cP) (x := 487) (by norm_num), get12 (A := LR 6) h1, get12 (A := LR 6) h2,
    get12 (A := LR 6) h3, get12 (A := LR 12) h2, get12 (A := LR 0) (x := 2) (by norm_num),
    get12 (A := LR 0) (x := 8) (by norm_num)]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨Nat.eq_of_beq_eq_true l1, Nat.eq_of_beq_eq_true l2⟩, Nat.eq_of_beq_eq_true l3⟩,
    Nat.eq_of_beq_eq_true l4⟩, Nat.eq_of_beq_eq_true l5⟩, Nat.eq_of_beq_eq_true l6⟩, ?_⟩
  decide +kernel

end CertificateChecks.KernelCo2Smith
