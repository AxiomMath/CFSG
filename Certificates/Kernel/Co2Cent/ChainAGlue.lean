module

public import Certificates.Kernel.Co2Cent.Head
public import Certificates.Kernel.Co2Cent.Trees
public import Certificates.Kernel.Co2Cent.CentChk
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.OrbRow.Tight
public import CFSG.Certificates.Kernel.OrbRow.ReachPerm
public import CFSG.Certificates.Kernel.OrbRow.LevelSound
public import CFSG.Sporadic.Co2Cert.Order
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

@[expose] noncomputable def SAarr : Array (Array Nat) :=
  Array.ofFn (n := 16) fun j => unpack 2300 12 (getS SA j.val)

@[expose] noncomputable def BAarr : Array Nat :=
  Array.ofFn (n := 10) fun t => pg 12 (mask 12) (packB 12 BA) t.val

@[expose] noncomputable def sA (j : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (unpack 2300 12 (getS SA j))

theorem SAarr_get {j : ℕ} (hj : j < 16) : SAarr[j]! = unpack 2300 12 (getS SA j) := by
  rw [getElem!_pos SAarr j (by simp [SAarr]; omega)]
  simp [SAarr]

theorem bindsA : Binds 2300 12 (getS SA) 16 10 (packB 12 BA) SAarr BAarr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SAarr], fun j hj => SAarr_get hj,
    by simp [BAarr], fun t ht => ?_⟩
  rw [getElem!_pos BAarr t (by simp [BAarr]; omega)]
  simp [BAarr]

theorem headA : ∃ SI : List ℕ, headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SA)
    (getS SI) 16 2 dA 10 (packB 12 BA) = true :=
  invsF_sound (c := fun SI => headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) (getS SA)
    (getS SI) 16 2 dA 10 (packB 12 BA)) ch17351_hA

theorem hdA : ∃ W, Hd 2300 SAarr BAarr 2 W := by
  obtain ⟨SI, hh⟩ := headA
  obtain ⟨hk, hH⟩ := rawHeadOK_of bindsA hh
  exact ⟨_, hd_of_head hk hH⟩

theorem prepA {j : ℕ} (hj : j < 16) : PRep 2300 12 (getS SA j) (sA j) := by
  obtain ⟨W, hd⟩ := hdA
  have h := rep_S hd (j := j) (by simp [SAarr]; omega)
  rw [SAarr_get hj] at h
  exact prep_of_rep h

theorem sA_apply {j : ℕ} (hj : j < 16) (y : ℕ) (hy : y < 2300) :
    ((sA j) ⟨y, hy⟩ : ℕ) = pg 12 4095 (getS SA j) y :=
  (prepA hj ⟨y, hy⟩).symm

theorem oA01 : getS SA 0 = CertificateChecks.KernelSpor.Co2A.S 0 ∧
    getS SA 1 = CertificateChecks.KernelSpor.Co2A.S 1 := by
  have h := ch17351_oAB
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩

theorem oA0 : getS SA 0 = CertificateChecks.KernelSpor.Co2A.S 0 := oA01.1

theorem oA1 : getS SA 1 = CertificateChecks.KernelSpor.Co2A.S 1 := oA01.2

theorem gen_le : Gen 2300 SAarr 2 ≤ co2P := by
  rw [Gen, closure_le]
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  have e0 : permOfArr 2300 SAarr[0]! = co2Gen 0 := by
    rw [SAarr_get (by norm_num), oA0, co2Gen, CertificateChecks.KernelSpor.Co2Order.a_eq 0
      (by norm_num)]
  have e1 : permOfArr 2300 SAarr[1]! = co2Gen 1 := by
    rw [SAarr_get (by norm_num), oA1, co2Gen, CertificateChecks.KernelSpor.Co2Order.a_eq 1
      (by norm_num)]
  interval_cases j
  · change permOfArr 2300 SAarr[0]! ∈ co2P
    rw [e0]
    exact subset_closure (Set.mem_insert _ _)
  · change permOfArr 2300 SAarr[1]! ∈ co2P
    rw [e1]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sA_mem {j : ℕ} (hj : j < 16) : sA j ∈ co2P := by
  obtain ⟨W, hd⟩ := hdA
  have h := S_mem_Gen hd j (by simp [SAarr]; omega)
  rw [SAarr_get hj] at h
  exact gen_le h

theorem baseA_ok : allN 10 (fun t => Nat.blt (getS BA t) 2300) = true := by quickRfl

theorem lenBA : BA.length = 10 := by decide +kernel

theorem baseA_lt (t : ℕ) : getS BA t < 2300 := by
  rcases Nat.lt_or_ge t 10 with ht | ht
  · exact Nat.le_of_ble_eq_true (allN_spec baseA_ok t ht)
  · rw [getS_eq, List.getD_eq_default _ _ (by rw [lenBA]; exact ht)]
    norm_num

@[expose] noncomputable def bA (t : ℕ) : Fin 2300 := ⟨getS BA t, baseA_lt t⟩

theorem bA_def (t : ℕ) : bA t = ⟨getS BA t, baseA_lt t⟩ := rfl

@[expose] noncomputable def GA (i : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (sA '' {j | lvOk 16 (getS MA i) j})

theorem MA10 : getS MA 10 = 0 := by decide +kernel

theorem not_lvOk_zero (j : ℕ) : ¬ lvOk 16 0 j := by
  rw [lvOk_iff, Nat.zero_testBit]
  simp

theorem GA10 : GA 10 = ⊥ := by
  rw [GA, MA10]
  have : sA '' {j | lvOk 16 0 j} = ∅ := by
    rw [Set.image_eq_empty]
    ext j
    exact ⟨fun h => not_lvOk_zero j h, fun h => h.elim⟩
  rw [this, Subgroup.closure_empty]

theorem closure_fixes {α : Type*} {X : Set (Equiv.Perm α)} {p : ℕ → α} {i : ℕ}
    (h : ∀ g ∈ X, ∀ t < i, g (p t) = p t) : ∀ g ∈ closure X, ∀ t < i, g (p t) = p t := by
  have hle : closure X ≤ stabB ⊤ p i := (closure_le _).2 fun g hg => ⟨mem_top g, h g hg⟩
  exact fun g hg => (hle hg).2

theorem GA_le (i : ℕ) : GA i ≤ co2P := by
  rw [GA, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact sA_mem (lvOk_iff.1 hj).1

theorem GA_fix : ∀ i ≤ 10, ∀ g ∈ GA i, ∀ t < i, g (bA t) = bA t := by
  intro i hi
  rcases Nat.lt_or_ge i 10 with hi' | hi'
  · refine closure_fixes ?_
    rintro _ ⟨j, hj, rfl⟩ t ht
    have hf : fixLvK 12 4095 SA 16 (getS MA i) BA i = true := allN_spec ch17351_fA i hi'
    rw [bA_def]
    exact fix_of_fixLvK hf sA (fun j' hj' y hy => sA_apply (lvOk_iff.1 hj').1 y hy) hj ht
      (baseA_lt t)
  · have : i = 10 := by omega
    subst this
    rw [GA10]
    intro g hg t _
    rw [(mem_bot).1 hg]
    rfl

theorem maskDec_sound {M : List ℕ} {nl : ℕ} (h : maskDecK M nl = true) {i : ℕ} (hi : i + 1 < nl)
    {j : ℕ} (hj : (getS M (i + 1)).testBit j = true) : (getS M i).testBit j = true := by
  have h1 := allN_spec h i (by change i < nl - 1; omega)
  change strictB (getS M (Nat.succ i)) (fun a => Nat.beq (Nat.land a (getS M i)) a) = true at h1
  rw [strictB_apply] at h1
  have h2 : getS M (i + 1) &&& getS M i = getS M (i + 1) := Nat.eq_of_beq_eq_true h1
  have h3 := congrArg (fun a => a.testBit j) h2
  simp only [Nat.testBit_land, hj, Bool.true_and] at h3
  exact h3

theorem maskA : maskDecK MA 10 = true := by
  have h := ch17351_m
  simp only [bAnd_iff] at h
  exact h.1

theorem GA_dec : ∀ i < 10, GA (i + 1) ≤ GA i := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) 10 with hi' | hi'
  · refine closure_mono (Set.image_mono fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := lvOk_iff.1 hj
    exact lvOk_iff.2 ⟨hj1, maskDec_sound maskA hi' hj2⟩
  · have : i = 9 := by omega
    subst this
    rw [GA10]
    exact bot_le

theorem GA_orb : ∀ i < 10, ∃ s : Finset (Fin 2300), s.card = getS KA i ∧
    ∀ x ∈ s, ∃ g ∈ GA i, g (bA i) = x := by
  intro i hi
  have h : levelK 2300 12 4095 SA 16 BA KA MA DA RA i = true := allN_spec ch17351_tA i hi
  rw [levelK_eq] at h
  rw [bA_def]
  unfold GA
  exact orbit_of_rowsK h sA (fun j hj y hy => sA_apply (lvOk_iff.1 hj).1 y hy) (baseA_lt i)

theorem prodKA : ∏ t ∈ Finset.range 10, getS KA t = 42305421312000 := by decide +kernel

theorem chainA :
    ∀ i ≤ 10, GA i = stabB co2P bA i ∧ Nat.card (GA i) = ∏ t ∈ Finset.Ico i 10, getS KA t :=
  tight_chain co2P bA 10 GA (getS KA) (fun i _ => GA_le i) GA_fix GA_dec GA_orb
    (by rw [card_co2P, prodKA])

theorem prodKA5 : ∏ t ∈ Finset.Ico 5 10, getS KA t = 7776 := by decide +kernel

theorem card_GA5 :
    Nat.card (GA 5) = 7776 := by
  rw [(chainA 5 (by norm_num)).2, prodKA5]

theorem GA5_eq :
    GA 5 = stabB co2P bA 5 :=
  (chainA 5 (by norm_num)).1

theorem eq_one_of_fixA
    {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) (hfix : ∀ t < 10, g (bA t) = bA t) : g = 1 := by
  have h := chainA 10 le_rfl
  have hm : g ∈ GA 10 := by
    rw [h.1]
    exact ⟨hg, hfix⟩
  rw [GA10] at hm
  exact (mem_bot).1 hm

end CertificateChecks.KernelCo2Cent

end
