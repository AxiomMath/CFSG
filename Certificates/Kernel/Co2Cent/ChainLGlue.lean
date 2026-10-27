module

public import Certificates.Kernel.Co2Cent.ChainAGlue
public import CFSG.Certificates.Kernel.OrbRow.CentLGrp
public import CFSG.Certificates.Kernel.OrbRow.CentBSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

@[expose] noncomputable def SLarr : Array (Array Nat) :=
  Array.ofFn (n := 6) fun j => unpack 2300 12 (getS SL j.val)

@[expose] noncomputable def BLarr : Array Nat :=
  Array.ofFn (n := 3) fun t => pg 12 (mask 12) (packB 12 BL) t.val

@[expose] noncomputable def sL (j : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (unpack 2300 12 (getS SL j))

@[expose] noncomputable def uvL (i : Fin 2) : Equiv.Perm (Fin 2300) := sL i.val

@[expose] noncomputable def Lg : Subgroup (Equiv.Perm (Fin 2300)) := closure (Set.range uvL)

theorem SLarr_get {j : ℕ} (hj : j < 6) : SLarr[j]! = unpack 2300 12 (getS SL j) := by
  rw [getElem!_pos SLarr j (by simp [SLarr]; omega)]
  simp [SLarr]

theorem bindsLg : Binds 2300 12 (getS SL) 6 3 (packB 12 BL) SLarr BLarr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SLarr], fun j hj => SLarr_get hj,
    by simp [BLarr], fun t ht => ?_⟩
  rw [getElem!_pos BLarr t (by simp [BLarr]; omega)]
  simp [BLarr]

theorem headL : ∃ SI : List ℕ, headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SL)
    (getS SI) 6 2 dL 3 (packB 12 BL) = true :=
  invsF_sound (c := fun SI => headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SL)
    (getS SI) 6 2 dL 3 (packB 12 BL)) ch17351_hL

theorem hdL : ∃ W, Hd 2300 SLarr BLarr 2 W := by
  obtain ⟨SI, hh⟩ := headL
  obtain ⟨hk, hH⟩ := rawHeadOK_of bindsLg hh
  exact ⟨_, hd_of_head hk hH⟩

theorem prepL {j : ℕ} (hj : j < 6) : PRep 2300 12 (getS SL j) (sL j) := by
  obtain ⟨W, hd⟩ := hdL
  have h := rep_S hd (j := j) (by simp [SLarr]; omega)
  rw [SLarr_get hj] at h
  exact prep_of_rep h

theorem sL_apply {j : ℕ} (hj : j < 6) (y : ℕ) (hy : y < 2300) :
    ((sL j) ⟨y, hy⟩ : ℕ) = pg 12 4095 (getS SL j) y :=
  (prepL hj ⟨y, hy⟩).symm

theorem genL_eq : Gen 2300 SLarr 2 = Lg := by
  have e : (fun j : Fin 2 => permOfArr 2300 SLarr[j.val]!) = uvL := by
    funext j
    rw [uvL, sL, SLarr_get (by omega)]
  rw [Gen, Lg, e]

theorem sL_mem {j : ℕ} (hj : j < 6) : sL j ∈ Lg := by
  obtain ⟨W, hd⟩ := hdL
  have h := S_mem_Gen hd j (by simp [SLarr]; omega)
  rw [SLarr_get hj, genL_eq] at h
  exact h

theorem baseL_ok : allN 3 (fun t => Nat.blt (getS BL t) 2300) = true := by quickRfl

theorem lenBL : BL.length = 3 := by decide +kernel

theorem baseL_lt (t : ℕ) : getS BL t < 2300 := by
  rcases Nat.lt_or_ge t 3 with ht | ht
  · exact Nat.le_of_ble_eq_true (allN_spec baseL_ok t ht)
  · rw [getS_eq, List.getD_eq_default _ _ (by rw [lenBL]; exact ht)]
    norm_num

@[expose] noncomputable def bL (t : ℕ) : Fin 2300 := ⟨getS BL t, baseL_lt t⟩

theorem bL_def (t : ℕ) : bL t = ⟨getS BL t, baseL_lt t⟩ := rfl

@[expose] noncomputable def GLc (i : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (sL '' {j | lvOk 6 (getS ML i) j})

theorem ML3 : getS ML 3 = 0 := by decide +kernel

theorem GLc3 : GLc 3 = ⊥ := by
  rw [GLc, ML3]
  have : sL '' {j | lvOk 6 0 j} = ∅ := by
    rw [Set.image_eq_empty]
    ext j
    refine ⟨fun h => ?_, fun h => h.elim⟩
    have := (lvOk_iff.1 h).2
    rw [Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  rw [this, Subgroup.closure_empty]

theorem GLc_le (i : ℕ) : GLc i ≤ Lg := by
  rw [GLc, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact sL_mem (lvOk_iff.1 hj).1

theorem GLc_fix : ∀ i ≤ 3, ∀ g ∈ GLc i, ∀ t < i, g (bL t) = bL t := by
  intro i hi
  rcases Nat.lt_or_ge i 3 with hi' | hi'
  · refine closure_fixes ?_
    rintro _ ⟨j, hj, rfl⟩ t ht
    have hf : fixLvK 12 4095 SL 6 (getS ML i) BL i = true := allN_spec ch17351_fL i hi'
    rw [bL_def]
    exact fix_of_fixLvK hf sL (fun j' hj' y hy => sL_apply (lvOk_iff.1 hj').1 y hy) hj ht
      (baseL_lt t)
  · have : i = 3 := by omega
    subst this
    rw [GLc3]
    intro g hg t _
    rw [(mem_bot).1 hg]
    rfl

theorem maskL : maskDecK ML 3 = true := by
  have h := ch17351_m
  simp only [bAnd_iff] at h
  exact h.2.2

theorem GLc_dec : ∀ i < 3, GLc (i + 1) ≤ GLc i := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) 3 with hi' | hi'
  · refine closure_mono (Set.image_mono fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := lvOk_iff.1 hj
    exact lvOk_iff.2 ⟨hj1, maskDec_sound maskL hi' hj2⟩
  · have : i = 2 := by omega
    subst this
    rw [GLc3]
    exact bot_le

theorem rowsL {i : ℕ} (hi : i < 3) : rowsK 2300 12 4095 SL 6 (getS ML i) (getS DL i) (getS BL i)
    (getS KL i) (getLs RL i) = true := by
  have h : levelK 2300 12 4095 SL 6 BL KL ML DL RL i = true := allN_spec ch17351_tL i hi
  rw [levelK_eq] at h
  exact h

theorem GLc_orb : ∀ i < 3, ∃ s : Finset (Fin 2300), s.card = getS KL i ∧
    ∀ x ∈ s, ∃ g ∈ GLc i, g (bL i) = x := by
  intro i hi
  rw [bL_def]
  unfold GLc
  exact orbit_of_rowsK (rowsL hi) sL (fun j hj y hy => sL_apply (lvOk_iff.1 hj).1 y hy)
    (baseL_lt i)

theorem reach_L {i : ℕ} (hi : i < 3) {y : Fin 2300} (hy : depD (getS DL i) y ≠ 255) :
    ∃ h ∈ GLc i, h (bL i) = y := by
  obtain ⟨hyn, g, hg, hgy⟩ := reach_perm sL (fun j hj z hz => sL_apply (lvOk_iff.1 hj).1 z hz)
    (baseL_lt i) ((rowsK_dep (rowsL hi)).2 y y.2 hy)
  exact ⟨g, hg, by rw [bL_def]; exact hgy⟩

theorem prodKL : ∏ t ∈ Finset.Ico 0 3, getS KL t = 25920 := by decide +kernel

theorem card_Lg_ge : 25920 ≤ Nat.card Lg := by
  have h := CentLGrp.prod_le_card_chain bL 3 GLc (getS KL) GLc_fix GLc_dec GLc_orb 0 (by norm_num)
  rw [prodKL] at h
  exact h.trans (Subgroup.card_le_of_le (GLc_le 0))

end CertificateChecks.KernelCo2Cent

end
