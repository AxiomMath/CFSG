module

public import Certificates.Kernel.D42.PGlue
public import Certificates.Kernel.D42.PUKU0
public import Certificates.Kernel.D42.PUKU1
import CFSG.Certificates.Kernel.BfsPinAlg

public section

set_option maxRecDepth 400000

namespace CFSG.KD.D42

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

theorem hid360 : idT 360 = tabT (unpack 360 9 (pidn 360 9)) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hn360]

theorem hidc360 : canonK 360 9 (mask 9) (360 * 9) (pidn 360 9) = true :=
  (CFSG.KC.BfsPin.PP.id hn360).1

theorem pTabs {j : Nat} (hj : j < 2) {G GI GJ : Nat → Nat} (hgen : genP G GI GJ j = true) :
    (∀ l < 2, G l = pidn 360 9) ∧ TabsOK 360 9 2 GI (pGens j).toArray ∧
      (∀ l < 2, invEqK 360 9 (mask 9) (360 * 9) (GI l) (GJ l) = true ∧
        canonK 360 9 (mask 9) (360 * 9) (GJ l) = true) := by
  have hg : ∀ l < 2, G l = pidn 360 9 ∧ GI l =
      wA ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j []).getD l []) ∧
      invSK (GI l) (GJ l) = true := by
    intro l hl
    have := allN_spec hgen l hl
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1⟩
  have hlet : ∀ w ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j [],
      lettersK 18 w = true := by
    interval_cases j <;> decide
  refine ⟨fun l hl => (hg l hl).1, ⟨by simp [pGens_len j hj], fun l hl => ⟨?_,
    (invSK_spec (hg l hl).2.2).1⟩⟩, fun l hl =>
    ⟨(invSK_spec (hg l hl).2.2).2.2, (invSK_spec (hg l hl).2.2).2.1⟩⟩
  have hlen : l < (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.pWords.getD j []).length := by
    have := pGens_len j hj
    unfold pGens at this
    rw [List.length_map] at this
    omega
  rw [getElem!_pos _ l (by simpa [pGens_len j hj] using hl), List.getElem_toArray]
  simp only [pGens, List.getElem_map]
  rw [autW_eq (hlet _ (List.getElem_mem hlen)), arrTable_unpack9, (hg l hl).2.1,
    List.getD_eq_getElem _ _ hlen]

@[expose] noncomputable def cgList (j : Nat) : List Table :=
  (CFSG.ClassicalInvolution.O8Data.centGens.getD (mainIdx j) []).map
    fun w => CFSG.ComponentClassification.J2Cover.arrTable 360 (CFSG.EvenSmallLie.OmegaEight.omegaW w)

theorem cgTbls_eq (j : Nat) : cgTbls j = cgList j ++ (cgList j).map (invT 360) := rfl

theorem centGens_len {j : Nat} (hj : j < 2) :
    (CFSG.ClassicalInvolution.O8Data.centGens.getD (mainIdx j) []).length = 3 := by
  interval_cases j <;> rfl

theorem cgList_len {j : Nat} (hj : j < 2) : (cgList j).length = 3 := by
  rw [cgList, List.length_map, centGens_len hj]

theorem centGens_let {j : Nat} (hj : j < 2) :
    ∀ w ∈ CFSG.ClassicalInvolution.O8Data.centGens.getD (mainIdx j) [], lettersK 17 w = true := by
  interval_cases j <;> decide

theorem cg_tab {j : Nat} (hj : j < 2) {m : Nat} (hm : m < (cgList j).length) :
    (cgList j)[m] = tabT (unpack 360 9 (cgK (mainIdx j) m)) := by
  have hm' : m < (CFSG.ClassicalInvolution.O8Data.centGens.getD (mainIdx j) []).length := by
    rw [centGens_len hj]
    rw [cgList_len hj] at hm
    exact hm
  simp only [cgList]
  rw [List.getElem_map, omegaW_eq (centGens_let hj _ (List.getElem_mem hm')), arrTable_unpack9, cgK,
    List.getD_eq_getElem _ _ hm']

theorem cgTbls_get {j : Nat} (hj : j < 2)
    (h3 : allN 3 (fun l => invSK (cgK (mainIdx j) l) (pinv (cgK (mainIdx j) l))) = true)
    {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) :
    (cgTbls j).getD (l - 1) (idT 360) = tabT (unpack 360 9 (SU (mainIdx j) l)) ∧
      canonK 360 9 (mask 9) (360 * 9) (SU (mainIdx j) l) = true := by
  have hlen := cgList_len hj
  rw [cgTbls_eq]
  by_cases hl : l < 4
  · have hb : Nat.blt l 4 = true := Nat.blt_eq.mpr hl
    have e : SU (mainIdx j) l = cgK (mainIdx j) (l - 1) := by
      unfold SU
      rw [hb]
      rfl
    rw [e, List.getD_eq_getElem _ _ (by simp [hlen]; omega),
      List.getElem_append_left (by simp [hlen]; omega), cg_tab hj]
    exact ⟨rfl, (invSK_spec (allN_spec h3 (l - 1) (by omega))).1⟩
  · have hb : Nat.blt l 4 = false := by
      cases e : Nat.blt l 4
      · rfl
      · exact absurd (Nat.blt_eq.mp e) hl
    have e : SU (mainIdx j) l = pinv (cgK (mainIdx j) (l - 4)) := by
      unfold SU
      rw [hb]
      rfl
    have hs := invSK_spec (allN_spec h3 (l - 4) (by omega))
    have key : ∀ (k : Nat) (hk : k < (cgList j).length), k = l - 4 →
        invT 360 (cgList j)[k] = tabT (unpack 360 9 (pinv (cgK (mainIdx j) (l - 4)))) := by
      rintro k hk rfl
      rw [cg_tab hj, invT_unpack (lt_of_canonK hs.1) hs.2.2]
    rw [e, List.getD_eq_getElem _ _ (by simp [hlen]; omega),
      List.getElem_append_right (by simp [hlen]; omega), List.getElem_map]
    exact ⟨key _ _ (by rw [hlen]; omega), hs.2.1⟩

theorem uTabs {j : Nat} (hj : j < 2) {k : Nat} {G GI GJ : Nat → Nat}
    (hk : (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).length = k)
    (hgen : genU G GI GJ j (mainIdx j) k = true) :
    (∀ r < k, G r = pidn 360 9 ∧ invSK (GI r) (GJ r) = true ∧ commK (GI r) (zK j) = true ∧
      siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 (GI r) = true) ∧
      TabsOK 360 9 k GI (uGens j).toArray ∧
      (∀ r < k, invEqK 360 9 (mask 9) (360 * 9) (GI r) (GJ r) = true ∧
        canonK 360 9 (mask 9) (360 * 9) (GJ r) = true) := by
  have hgu := hgen
  unfold genU at hgu
  simp only [bAnd_iff] at hgu
  obtain ⟨h3, hall⟩ := hgu
  have hg : ∀ r < k, G r = pidn 360 9 ∧ GI r = wfoldK 360 9 (mask 9) (SU (mainIdx j))
      ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).getD r [])
      (pidn 360 9) ∧ invSK (GI r) (GJ r) = true ∧ commK (GI r) (zK j) = true ∧
      siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 (GI r) = true := by
    intro r hr
    have := allN_spec hall r hr
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1,
      this.2.2.2.1, this.2.2.2.2⟩
  have hletU : ∀ w ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j [],
      ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6 := by
    interval_cases j <;> decide
  have hulen : (uGens j).length = k := by
    rw [uGens, List.length_map, hk]
  have htabs : TabsOK 360 9 k GI (uGens j).toArray := by
    refine ⟨by simp [hulen], fun r hr => ?_⟩
    have hr' : r < (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).length :=
      hk ▸ hr
    rw [getElem!_pos _ r (by simpa [hulen] using hr), List.getElem_toArray]
    simp only [uGens, List.getElem_map]
    rw [(hg r hr).2.1, List.getD_eq_getElem _ _ hr']
    exact wordTbl_unpack hid360 hidc360 fun l hl =>
      cgTbls_get hj h3 (hletU _ (List.getElem_mem hr') l hl).1 (hletU _ (List.getElem_mem hr') l hl).2
  have hgj : ∀ r < k, invEqK 360 9 (mask 9) (360 * 9) (GI r) (GJ r) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (GJ r) = true := fun r hr =>
    ⟨(invSK_spec (hg r hr).2.2.1).2.2, (invSK_spec (hg r hr).2.2.1).2.1⟩
  exact ⟨fun r hr => ⟨(hg r hr).1, (hg r hr).2.2⟩, htabs, hgj⟩

theorem u_of {j : Nat} (hj : j < 2) {k cnt : Nat}
    {G GI GJ T PL POS SRT SRI HS HSI CL NP PG PGI PGJ : Nat → Nat}
    (hk : (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).length = k)
    (hgen : genU G GI GJ j (mainIdx j) k = true) (hpg : genP PG PGI PGJ j = true)
    (hh : penumHdK (pidn 360 9) cnt 512 T PL = true)
    (hp : ∀ i < cnt, penumPtK 360 9 (mask 9) (360 * 9) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 360 9 (mask 9) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 360 9 (mask 9) (k + k) T (bothK k GI GJ)) CL c = true)
    (hnq : ∀ c < cnt * 2, findPtK cnt T (conjQK 360 9 (mask 9) 2 T PGI PGJ) NP c = true)
    (hm : cnt = 512) : uCheck j = true := by
  obtain ⟨hg, htabs, hgj⟩ := uTabs hj hk hgen
  obtain ⟨ez, hzc⟩ := zTbl_eq hj
  obtain ⟨-, hptabs, hpgj⟩ := pTabs hj hpg
  unfold uCheck
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun g hgm => ?_, enumOK_of hn360 (fun r hr => (hg r hr).1) htabs hgj hh hp hs hcl hm⟩,
    normOK_of hn360 (fun r hr => (hg r hr).1) htabs hh hp hs hptabs hpgj hnq⟩
  obtain ⟨r, hr, rfl, hc⟩ := TabsOK_list htabs hgm
  obtain ⟨-, -, hinv⟩ := invSK_spec (hg r hr).2.1
  refine ⟨⟨permOK_unpack hc hinv, ?_⟩, ?_⟩
  · have hcn := hc
    unfold canonK at hcn
    simp only [bAnd_iff] at hcn
    unfold siftOmega omegaLevels
    rw [natArr_tabT hc, siftK_eq chainOmP.1 (perm_of_head chainOmP.2.1) chainOmP.2.2.1 rfl
      (Nat.eq_of_beq_eq_true hcn.2.1) hcn.2.2]
    exact (hg r hr).2.2.2
  · rw [ez, commTT_unpack hc hzc]
    exact (hg r hr).2.2.1

theorem peU0_all : ∀ s < 16, peU0 s = true := by
  intro s hs
  interval_cases s
  exacts [peU00, peU01, peU02, peU03, peU04, peU05, peU06, peU07, peU08, peU09, peU010, peU011,
    peU012, peU013, peU014, peU015]

theorem peU1_all : ∀ s < 16, peU1 s = true := by
  intro s hs
  interval_cases s
  exacts [peU10, peU11, peU12, peU13, peU14, peU15, peU16, peU17, peU18, peU19, peU110, peU111,
    peU112, peU113, peU114, peU115]

theorem hsU_all : ∀ s < 4, hsU s = true := by
  intro s hs
  interval_cases s
  exacts [hsU0, hsU1, hsU2, hsU3]

theorem nqU_all : ∀ s < 8, nqU s = true := by
  intro s hs
  interval_cases s
  exacts [nqU0, nqU1, nqU2, nqU3, nqU4, nqU5, nqU6, nqU7]

theorem clU0_all : ∀ s < 32, clU0 s = true := by
  intro s hs
  interval_cases s
  exacts [clU00, clU01, clU02, clU03, clU04, clU05, clU06, clU07, clU08, clU09, clU010, clU011,
    clU012, clU013, clU014, clU015, clU016, clU017, clU018, clU019, clU020, clU021, clU022, clU023,
    clU024, clU025, clU026, clU027, clU028, clU029, clU030, clU031]

theorem clU1_all : ∀ s < 24, clU1 s = true := by
  intro s hs
  interval_cases s
  exacts [clU10, clU11, clU12, clU13, clU14, clU15, clU16, clU17, clU18, clU19, clU110, clU111,
    clU112, clU113, clU114, clU115, clU116, clU117, clU118, clU119, clU120, clU121, clU122, clU123]

theorem U0_cnt : U0.cnt = 512 := by
  have hb := baseP0
  simp only [bAnd_iff] at hb
  exact Nat.eq_of_beq_eq_true hb.2.2.2.2.2.1

theorem U1_cnt : U1.cnt = 512 := by
  have hb := baseP1
  simp only [bAnd_iff] at hb
  exact Nat.eq_of_beq_eq_true hb.2.2.2.2.2.1

theorem U0_pe : ∀ i < U0.cnt,
    penumPtK 360 9 (mask 9) (360 * 9) true U0.G U0.GI 8 U0.cnt U0.T U0.PL U0.POS U0.SRT U0.SRI i =
      true := by
  intro i hi
  have hi' : i < 512 := U0_cnt ▸ hi
  exact CFSG.KS.BaseMask.penumSl_spec (peU0_all (i / 32) (by omega))
    (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem U1_pe : ∀ i < U1.cnt,
    penumPtK 360 9 (mask 9) (360 * 9) true U1.G U1.GI 6 U1.cnt U1.T U1.PL U1.POS U1.SRT U1.SRI i =
      true := by
  intro i hi
  have hi' : i < 512 := U1_cnt ▸ hi
  exact CFSG.KS.BaseMask.penumSl_spec (peU1_all (i / 32) (by omega))
    (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem U0_hs : ∀ i < U0.cnt, hsortPtK 360 9 (mask 9) U0.cnt U0.T U0.HS U0.HSI i = true := by
  intro i hi
  have hi' : i < 512 := U0_cnt ▸ hi
  have h := hsU_all (i / 128) (by omega)
  unfold hsU at h
  simp only [bAnd_iff] at h
  exact slK_spec h.1 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem U1_hs : ∀ i < U1.cnt, hsortPtK 360 9 (mask 9) U1.cnt U1.T U1.HS U1.HSI i = true := by
  intro i hi
  have hi' : i < 512 := U1_cnt ▸ hi
  have h := hsU_all (i / 128) (by omega)
  unfold hsU at h
  simp only [bAnd_iff] at h
  exact slK_spec h.2 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem uCheck_k0 : uCheck 0 = true := by
  have hb := baseP0
  simp only [bAnd_iff] at hb
  obtain ⟨-, -, -, hgp, -, -, hh, hg⟩ := hb
  refine u_of (j := 0) (k := 8) (CL := U0Cl) (NP := U0N) (by norm_num) rfl hg hgp
    hh U0_pe U0_hs (fun c hc => ?_) (fun c hc => ?_) U0_cnt
  · have hc' : c < 512 * 16 := by have := U0_cnt; omega
    exact slK_spec (clU0_all (c / 256) (by omega)) c (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
  · have hc' : c < 512 * 2 := by have := U0_cnt; omega
    have h := nqU_all (c / 128) (by omega)
    unfold nqU at h
    simp only [bAnd_iff] at h
    exact slK_spec h.1 c (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega)

theorem uCheck_k1 : uCheck 1 = true := by
  have hb := baseP1
  simp only [bAnd_iff] at hb
  obtain ⟨-, -, -, hgp, -, -, hh, hg⟩ := hb
  refine u_of (j := 1) (k := 6) (CL := U1Cl) (NP := U1N) (by norm_num) rfl hg hgp
    hh U1_pe U1_hs (fun c hc => ?_) (fun c hc => ?_) U1_cnt
  · have hc' : c < 512 * 12 := by have := U1_cnt; omega
    exact slK_spec (clU1_all (c / 256) (by omega)) c (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
  · have hc' : c < 512 * 2 := by have := U1_cnt; omega
    have h := nqU_all (c / 128) (by omega)
    unfold nqU at h
    simp only [bAnd_iff] at h
    exact slK_spec h.2 c (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega)

end CFSG.KD.D42

end
