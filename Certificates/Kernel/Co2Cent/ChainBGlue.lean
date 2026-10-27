module

public import Certificates.Kernel.Co2Cent.ChainAGlue
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

@[expose] noncomputable def SBarr : Array (Array Nat) :=
  Array.ofFn (n := 17) fun j => unpack 2300 12 (getS SB j.val)

@[expose] noncomputable def BBarr : Array Nat :=
  Array.ofFn (n := 7) fun t => pg 12 (mask 12) (packB 12 BB) t.val

@[expose] noncomputable def sB (j : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (unpack 2300 12 (getS SB j))

theorem SBarr_get {j : ℕ} (hj : j < 17) : SBarr[j]! = unpack 2300 12 (getS SB j) := by
  rw [getElem!_pos SBarr j (by simp [SBarr]; omega)]
  simp [SBarr]

theorem bindsB : Binds 2300 12 (getS SB) 17 7 (packB 12 BB) SBarr BBarr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SBarr], fun j hj => SBarr_get hj,
    by simp [BBarr], fun t ht => ?_⟩
  rw [getElem!_pos BBarr t (by simp [BBarr]; omega)]
  simp [BBarr]

theorem headB : ∃ SI : List ℕ, headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SB)
    (getS SI) 17 2 dB 7 (packB 12 BB) = true :=
  invsF_sound (c := fun SI => headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SB)
    (getS SI) 17 2 dB 7 (packB 12 BB)) ch17351_hB

theorem hdB : ∃ W, Hd 2300 SBarr BBarr 2 W := by
  obtain ⟨SI, hh⟩ := headB
  obtain ⟨hk, hH⟩ := rawHeadOK_of bindsB hh
  exact ⟨_, hd_of_head hk hH⟩

theorem prepB {j : ℕ} (hj : j < 17) : PRep 2300 12 (getS SB j) (sB j) := by
  obtain ⟨W, hd⟩ := hdB
  have h := rep_S hd (j := j) (by simp [SBarr]; omega)
  rw [SBarr_get hj] at h
  exact prep_of_rep h

theorem sB_apply {j : ℕ} (hj : j < 17) (y : ℕ) (hy : y < 2300) :
    ((sB j) ⟨y, hy⟩ : ℕ) = pg 12 4095 (getS SB j) y :=
  (prepB hj ⟨y, hy⟩).symm

theorem oB01 : getS SB 0 = CertificateChecks.KernelSpor.Co2A.S 0 ∧
    getS SB 1 = CertificateChecks.KernelSpor.Co2A.S 1 := by
  have h := ch17351_oAB
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.1⟩

theorem genB_le : Gen 2300 SBarr 2 ≤ co2P := by
  rw [Gen, closure_le]
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  have e0 : permOfArr 2300 SBarr[0]! = co2Gen 0 := by
    rw [SBarr_get (by norm_num), oB01.1, co2Gen, CertificateChecks.KernelSpor.Co2Order.a_eq 0
      (by norm_num)]
  have e1 : permOfArr 2300 SBarr[1]! = co2Gen 1 := by
    rw [SBarr_get (by norm_num), oB01.2, co2Gen, CertificateChecks.KernelSpor.Co2Order.a_eq 1
      (by norm_num)]
  interval_cases j
  · change permOfArr 2300 SBarr[0]! ∈ co2P
    rw [e0]
    exact subset_closure (Set.mem_insert _ _)
  · change permOfArr 2300 SBarr[1]! ∈ co2P
    rw [e1]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sB_mem {j : ℕ} (hj : j < 17) : sB j ∈ co2P := by
  obtain ⟨W, hd⟩ := hdB
  have h := S_mem_Gen hd j (by simp [SBarr]; omega)
  rw [SBarr_get hj] at h
  exact genB_le h

theorem baseB_ok : allN 7 (fun t => Nat.blt (getS BB t) 2300) = true := by quickRfl

theorem lenBB : BB.length = 7 := by decide +kernel

theorem baseB_lt (t : ℕ) : getS BB t < 2300 := by
  rcases Nat.lt_or_ge t 7 with ht | ht
  · exact Nat.le_of_ble_eq_true (allN_spec baseB_ok t ht)
  · rw [getS_eq, List.getD_eq_default _ _ (by rw [lenBB]; exact ht)]
    norm_num

@[expose] noncomputable def bB (t : ℕ) : Fin 2300 := ⟨getS BB t, baseB_lt t⟩

theorem bB_def (t : ℕ) : bB t = ⟨getS BB t, baseB_lt t⟩ := rfl

@[expose] noncomputable def GB (i : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (sB '' {j | lvOk 17 (getS MB i) j})

theorem MB7 : getS MB 7 = 0 := by decide +kernel

theorem GB7 : GB 7 = ⊥ := by
  rw [GB, MB7]
  have : sB '' {j | lvOk 17 0 j} = ∅ := by
    rw [Set.image_eq_empty]
    ext j
    refine ⟨fun h => ?_, fun h => h.elim⟩
    have := (lvOk_iff.1 h).2
    rw [Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  rw [this, Subgroup.closure_empty]

theorem GB_le (i : ℕ) : GB i ≤ co2P := by
  rw [GB, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact sB_mem (lvOk_iff.1 hj).1

theorem GB_fix : ∀ i ≤ 7, ∀ g ∈ GB i, ∀ t < i, g (bB t) = bB t := by
  intro i hi
  rcases Nat.lt_or_ge i 7 with hi' | hi'
  · refine closure_fixes ?_
    rintro _ ⟨j, hj, rfl⟩ t ht
    have hf : fixLvK 12 4095 SB 17 (getS MB i) BB i = true := allN_spec ch17351_fB i hi'
    rw [bB_def]
    exact fix_of_fixLvK hf sB (fun j' hj' y hy => sB_apply (lvOk_iff.1 hj').1 y hy) hj ht
      (baseB_lt t)
  · have : i = 7 := by omega
    subst this
    rw [GB7]
    intro g hg t _
    rw [(mem_bot).1 hg]
    rfl

theorem maskB : maskDecK MB 7 = true := by
  have h := ch17351_m
  simp only [bAnd_iff] at h
  exact h.2.1

theorem GB_dec : ∀ i < 7, GB (i + 1) ≤ GB i := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) 7 with hi' | hi'
  · refine closure_mono (Set.image_mono fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := lvOk_iff.1 hj
    exact lvOk_iff.2 ⟨hj1, maskDec_sound maskB hi' hj2⟩
  · have : i = 6 := by omega
    subst this
    rw [GB7]
    exact bot_le

theorem GB_orb : ∀ i < 7, ∃ s : Finset (Fin 2300), s.card = getS KB i ∧
    ∀ x ∈ s, ∃ g ∈ GB i, g (bB i) = x := by
  intro i hi
  have h : levelK 2300 12 4095 SB 17 BB KB MB DB RB i = true := allN_spec ch17351_tB i hi
  rw [levelK_eq] at h
  rw [bB_def]
  unfold GB
  exact orbit_of_rowsK h sB (fun j hj y hy => sB_apply (lvOk_iff.1 hj).1 y hy) (baseB_lt i)

theorem prodKB : ∏ t ∈ Finset.range 7, getS KB t = 42305421312000 := by decide +kernel

theorem chainB :
    ∀ i ≤ 7, GB i = stabB co2P bB i ∧ Nat.card (GB i) = ∏ t ∈ Finset.Ico i 7, getS KB t :=
  tight_chain co2P bB 7 GB (getS KB) (fun i _ => GB_le i) GB_fix GB_dec GB_orb
    (by rw [card_co2P, prodKB])

theorem eq_one_of_fixB
    {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) (hfix : ∀ t < 7, g (bB t) = bB t) : g = 1 := by
  have h := chainB 7 le_rfl
  have hm : g ∈ GB 7 := by
    rw [h.1]
    exact ⟨hg, hfix⟩
  rw [GB7] at hm
  exact (mem_bot).1 hm

end CertificateChecks.KernelCo2Cent

end
