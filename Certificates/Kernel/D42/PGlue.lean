module

public import Certificates.Kernel.D42.PUK
public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.D42

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem hn360 : szOK 360 9 = true := by decide

theorem arrTable_unpack9 (X : Nat) :
    CFSG.ComponentClassification.J2Cover.arrTable 360 (unpack 360 9 X) = tabT (unpack 360 9 X) := by
  apply Array.ext (by simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack])
  intro i h1 h2
  simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack]

theorem invSK_spec {p r : Nat} (h : invSK p r = true) :
    canonK 360 9 (mask 9) (360 * 9) p = true ∧ canonK 360 9 (mask 9) (360 * 9) r = true ∧
      invEqK 360 9 (mask 9) (360 * 9) p r = true := by
  unfold invSK at h
  simp only [bAnd_iff] at h
  exact h

theorem zTbl_eq {j : Nat} (hj : j < 2) :
    zTbl j = tabT (unpack 360 9 (zK j)) ∧ canonK 360 9 (mask 9) (360 * 9) (zK j) = true := by
  have hi : mainIdx j < 5 := by unfold mainIdx; split_ifs <;> omega
  obtain ⟨e, hc, -⟩ := main_ok hi
  have hz : zK j = mainK (mainIdx j) := by
    interval_cases j <;> rfl
  rw [zTbl, e, arrTable_unpack9, hz]
  exact ⟨rfl, hc⟩

theorem pGens_len (j : Nat) (hj : j < 2) : (pGens j).length = 2 := by
  interval_cases j <;> rfl

theorem sylow_of {j : Nat} (hj : j < 2) {cnt : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (hgen : genP G GI GJ j = true)
    (hh : penumHdK (pidn 360 9) cnt (pOrder j) T PL = true)
    (hp : ∀ i < cnt, penumPtK 360 9 (mask 9) (360 * 9) true G GI 2 cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 360 9 (mask 9) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (2 + 2),
      findPtK cnt T (prodQK 360 9 (mask 9) (2 + 2) T (bothK 2 GI GJ)) CL c = true)
    (hm : cnt = pOrder j) : sylowCheck j = true := by
  have hg : ∀ l < 2, G l = pidn 360 9 ∧ GI l =
      wA ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j []).getD l []) ∧
      invSK (GI l) (GJ l) = true ∧ commK (GI l) (zK j) = true := by
    intro l hl
    have := allN_spec hgen l hl
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1, this.2.2.2⟩
  have hlet : ∀ w ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j [],
      CFSG.Monster.B.Co2.Native.lettersOK 18 w = true ∧ lettersK 18 w = true := by
    interval_cases j <;> decide
  have htabs : TabsOK 360 9 2 GI (pGens j).toArray := by
    refine ⟨by simp [pGens_len j hj], fun l hl => ⟨?_, (invSK_spec (hg l hl).2.2.1).1⟩⟩
    have hlen : l < (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j []).length := by
      have := pGens_len j hj
      unfold pGens at this
      rw [List.length_map] at this
      omega
    rw [getElem!_pos _ l (by simpa [pGens_len j hj] using hl), List.getElem_toArray]
    simp only [pGens, List.getElem_map]
    have hw := (hlet _ (List.getElem_mem hlen)).2
    rw [autW_eq hw, arrTable_unpack9, (hg l hl).2.1, List.getD_eq_getElem _ _ hlen]
  have hgj : ∀ l < 2, invEqK 360 9 (mask 9) (360 * 9) (GI l) (GJ l) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (GJ l) = true := fun l hl =>
    ⟨(invSK_spec (hg l hl).2.2.1).2.2, (invSK_spec (hg l hl).2.2.1).2.1⟩
  obtain ⟨ez, hzc⟩ := zTbl_eq hj
  unfold sylowCheck
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun w hw => (hlet w hw).1, fun g hgm => ?_⟩,
    enumOK_of hn360 (fun l hl => (hg l hl).1) htabs hgj hh hp hs hcl hm⟩
  obtain ⟨l, hl, rfl, hc⟩ := TabsOK_list htabs hgm
  obtain ⟨-, -, hinv⟩ := invSK_spec (hg l hl).2.2.1
  refine ⟨⟨permOK_unpack hc hinv, ?_⟩, ?_⟩
  · rw [invT_unpack (lt_of_canonK (hgj l hl).2) hinv]
    exact invOK_unpack hc (hgj l hl).2 hinv
  · rw [ez, commTT_unpack hc hzc]
    exact (hg l hl).2.2.2

theorem peP0_all : ∀ s < 6, peP0 s = true := by
  intro s hs
  interval_cases s
  exacts [peP00, peP01, peP02, peP03, peP04, peP05]

theorem sylowCheck_k0 : sylowCheck 0 = true := by
  have hb := baseP0
  simp only [bAnd_iff] at hb
  obtain ⟨-, hc, hh, hg, -⟩ := hb
  have hcnt : P0.cnt = 81 := Nat.eq_of_beq_eq_true hc
  have hS := hsP0
  have hC := clP0
  unfold CFSG.KD.D42.hsP at hS
  unfold CFSG.KD.D42.clP at hC
  simp only [bAnd_iff] at hS hC
  refine sylow_of (j := 0) (POS := P0.POS) (SRT := P0.SRT) (SRI := P0.SRI) (HS := P0.HS)
    (HSI := P0.HSI) (CL := P0Cl) (by norm_num) hg hh (fun i hi => ?_) (fun i hi => ?_)
    (fun c hc => ?_) hcnt
  · have hi' : i < 81 := hcnt ▸ hi
    exact CFSG.KS.BaseMask.penumSl_spec (peP0_all (i / 16) (by omega))
      (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi
  · have hi' : i < 81 := hcnt ▸ hi
    exact slK_spec hS.1 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi
  · have hc' : c < 81 * 4 := hcnt ▸ hc
    exact slK_spec hC.1 c (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega)

theorem sylowCheck_k1 : sylowCheck 1 = true := by
  have hb := baseP1
  simp only [bAnd_iff] at hb
  obtain ⟨-, hc, hh, hg, -⟩ := hb
  have hcnt : P1.cnt = 9 := Nat.eq_of_beq_eq_true hc
  have hS := hsP0
  have hC := clP0
  unfold CFSG.KD.D42.hsP at hS
  unfold CFSG.KD.D42.clP at hC
  simp only [bAnd_iff] at hS hC
  refine sylow_of (j := 1) (POS := P1.POS) (SRT := P1.SRT) (SRI := P1.SRI) (HS := P1.HS)
    (HSI := P1.HSI) (CL := P1Cl) (by norm_num) hg hh (fun i hi => ?_) (fun i hi => ?_)
    (fun c hc => ?_) hcnt
  · have hi' : i < 9 := hcnt ▸ hi
    exact CFSG.KS.BaseMask.penumSl_spec peP10 (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hi
  · have hi' : i < 9 := hcnt ▸ hi
    exact slK_spec hS.2 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi
  · have hc' : c < 9 * 4 := hcnt ▸ hc
    exact slK_spec hC.2 c (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega)

end CFSG.KD.D42

end
