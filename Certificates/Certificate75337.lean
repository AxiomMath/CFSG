module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3Pair
import Certificates.Kernel.Asch54.Co3Checks
import Certificates.Certificate2152
import Certificates.Certificate2158
import Certificates.Certificate2162
import CFSG.Certificates.Kernel.Asch54.Co3Sound
import CFSG.Certificates.Kernel.Spor.RawTreeSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Certificates.NativeSchreierCard
import CFSG.Sporadic.Schreier.Co3Sylow
import CFSG.Sporadic.Schreier.Co3Faithful
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSound

set_option maxRecDepth 400000

namespace CertificateChecks.Batch75337

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.LocalAnalysis.WeakClosure81.SporCo3
  CertificateChecks.KernelSpor CertificateChecks.KernelAsch54 CertificateChecks.KernelAsch54.Co3

theorem getElem!_append_left {a b : Array (Array ℕ)} {k : ℕ} (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by rw [Array.size_append]; omega), getElem!_pos a k hk,
    Array.getElem_append_left hk]

theorem getElem!_append_right {a b : Array (Array ℕ)} {k : ℕ} (hk : a.size ≤ k)
    (hk' : k < a.size + b.size) : (a ++ b)[k]! = b[k - a.size]! := by
  rw [getElem!_pos (a ++ b) k (by rw [Array.size_append]; omega),
    getElem!_pos b (k - a.size) (by omega), Array.getElem_append_right hk]

theorem tExt_size : (co3TArrs.extract 0 8).size = 8 := by
  simp [co3TArrs_size]

theorem pairAArrs_size : pairAArrs.size = 9 := by simp [pairAArrs]

theorem pairBArrs_size : pairBArrs.size = 10 := by simp [pairBArrs]

theorem tArr_get {j : ℕ} (hj : j < 10) : co3TArrs[j]! = unpack 276 9 (Co3Text.L (Nat.add 35 j)) :=
  (Co3Text.field_of (f := 5) (F := fun j => Co3Text.L (Nat.add 35 j)) rfl (by norm_num)
    (by quickRfl)).2 j hj

theorem pairLine {k : ℕ} (hk : k < 19) :
    hexLine pairText.toUTF8 3 276 k = unpack 276 9 (Co3PT.L k) := by
  rw [Co3PT.eq]
  have h := CFSG.KS.Text.hexBind_sound Co3PT.all k hk
  rwa [Nat.zero_add] at h

theorem aArr_get {j : ℕ} (hj : j < 9) : pairAArrs[j]! = unpack 276 9 (Co3PT.L j) := by
  rw [getElem!_pos _ j (by rw [pairAArrs_size]; exact hj), ← pairLine (by omega)]
  unfold pairAArrs
  exact Array.getElem_ofFn ..

theorem bArr_get {j : ℕ} (hj : j < 10) : pairBArrs[j]! = unpack 276 9 (Co3PT.L (9 + j)) := by
  rw [getElem!_pos _ j (by rw [pairBArrs_size]; exact hj), ← pairLine (by omega)]
  unfold pairBArrs
  exact Array.getElem_ofFn ..

theorem pairAS_size : pairAS.size = 17 := by
  rw [pairAS, Array.size_append, tExt_size, pairAArrs_size]

theorem pairBS_size : pairBS.size = 18 := by
  rw [pairBS, Array.size_append, tExt_size, pairBArrs_size]

theorem pairAS_lo {j : ℕ} (hj : j < 8) : pairAS[j]! = co3TArrs[j]! := by
  rw [pairAS, getElem!_append_left (by rw [tExt_size]; exact hj), co3TExtract_get hj]

theorem pairBS_lo {j : ℕ} (hj : j < 8) : pairBS[j]! = co3TArrs[j]! := by
  rw [pairBS, getElem!_append_left (by rw [tExt_size]; exact hj), co3TExtract_get hj]

theorem pairAS_hi {j : ℕ} (h1 : 8 ≤ j) (h2 : j < 17) : pairAS[j]! = pairAArrs[j - 8]! := by
  rw [pairAS, getElem!_append_right (by rw [tExt_size]; exact h1)
    (by rw [tExt_size, pairAArrs_size]; omega), tExt_size]

theorem pairBS_hi {j : ℕ} (h1 : 8 ≤ j) (h2 : j < 18) : pairBS[j]! = pairBArrs[j - 8]! := by
  rw [pairBS, getElem!_append_right (by rw [tExt_size]; exact h1)
    (by rw [tExt_size, pairBArrs_size]; omega), tExt_size]

theorem bq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem sA_get {j : ℕ} (hj : j < 17) : pairAS[j]! = unpack 276 9 (ch75337a.S j) := by
  rcases Nat.lt_or_ge j 8 with h | h
  · rw [pairAS_lo h, tArr_get (by omega), bq (Orb.allN_iff.1 lnTA j h)]
  · rw [pairAS_hi h hj, aArr_get (by omega)]
    have e := bq (Orb.allN_iff.1 lnA (j - 8) (by omega))
    rw [show 8 + (j - 8) = j by omega, Nat.add_eq, Nat.zero_add] at e
    rw [e]

theorem sB_get {j : ℕ} (hj : j < 18) : pairBS[j]! = unpack 276 9 (ch75337b.S j) := by
  rcases Nat.lt_or_ge j 8 with h | h
  · rw [pairBS_lo h, tArr_get (by omega), bq (Orb.allN_iff.1 lnTB j h)]
  · rw [pairBS_hi h hj, bArr_get (by omega)]
    have e := bq (Orb.allN_iff.1 lnB (j - 8) (by omega))
    rw [show 8 + (j - 8) = j by omega, Nat.add_eq] at e
    rw [e]

def baseAL : List ℕ := [0, 227, 154, 106, 1, 2, 3, 4, 5, 6]

def baseBL : List ℕ := [0, 106, 200, 28, 55, 1, 2, 3, 4, 5, 6]

theorem baseA_eq : ((co3FinList 276 (by decide) baseAL).map Fin.val).toArray =
    #[0, 227, 154, 106, 1, 2, 3, 4, 5, 6] := by decide

theorem baseB_eq : ((co3FinList 276 (by decide) baseBL).map Fin.val).toArray =
    #[0, 106, 200, 28, 55, 1, 2, 3, 4, 5, 6] := by decide

theorem bindsA : Binds 276 9 ch75337a.S 17 10 ch75337a.BP pairAS
    ((co3FinList 276 (by decide) baseAL).map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, pairAS_size, fun j hj => sA_get hj,
    by rw [baseA_eq]; rfl, fun t ht => ?_⟩
  rw [baseA_eq]
  exact bq (Orb.allN_iff.1 bgetA t ht)

theorem bindsB : Binds 276 9 ch75337b.S 18 11 ch75337b.BP pairBS
    ((co3FinList 276 (by decide) baseBL).map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, pairBS_size, fun j hj => sB_get hj,
    by rw [baseB_eq]; rfl, fun t ht => ?_⟩
  rw [baseB_eq]
  exact bq (Orb.allN_iff.1 bgetB t ht)

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_P_of {G : ℕ} {g : Array ℕ} (hg : g = unpack 276 9 G) {x : Equiv.Perm (Fin 276)}
    (hx : Rep 276 g x) (h : siftOne G = true) : x ∈ co3P := by
  have hs := and3 h
  refine mem_co3P_of_sift hx ?_
  rw [hg]
  exact CFSG.KC.B3S3K.siftA_of Co3C.binds Co3C.perm Co3C.hl hs

theorem PQ_lo {j : ℕ} (hj : j < 9) : PQ j = ch75337a.S (8 + j) := by simp [PQ, hj]

theorem PQ_hi {j : ℕ} (hj : 9 ≤ j) : PQ j = ch75337b.S (j - 1) := by
  simp [PQ, Nat.not_lt.2 hj]

theorem genA_mem {j : ℕ} (hj : j < 17) : permOfArr 276 pairAS[j]! ∈ co3P := by
  rcases Nat.lt_or_ge j 8 with h | h
  · rw [pairAS_lo h]
    exact co3T_le_P (co3TGen_mem h)
  · have hp := Orb.prep_PS bindsA (Orb.head_facts ch75337a.head).1 hj
    have hr := Orb.rep_unpack hp.1
    rw [← sA_get hj] at hr
    refine mem_P_of (sA_get hj) hr ?_
    have hs := Orb.allN_iff.1 siftQ (j - 8) (by omega)
    rwa [PQ_lo (by omega), show 8 + (j - 8) = j by omega] at hs

theorem genB_mem {j : ℕ} (hj : j < 18) : permOfArr 276 pairBS[j]! ∈ co3P := by
  rcases Nat.lt_or_ge j 8 with h | h
  · rw [pairBS_lo h]
    exact co3T_le_P (co3TGen_mem h)
  · have hp := Orb.prep_PS bindsB (Orb.head_facts ch75337b.head).1 hj
    have hr := Orb.rep_unpack hp.1
    rw [← sB_get hj] at hr
    refine mem_P_of (sB_get hj) hr ?_
    have hs := Orb.allN_iff.1 siftQ (j + 1) (by omega)
    rwa [PQ_hi (by omega), show j + 1 - 1 = j by omega] at hs

theorem sepA : Sep 276 pairAS ((co3FinList 276 (by decide) baseAL).map Fin.val).toArray := by
  refine CFSG.KS.Asch54.co3_sep (fun j hj => genA_mem (pairAS_size ▸ hj)) ?_
  rw [baseA_eq]
  decide

theorem sepB : Sep 276 pairBS ((co3FinList 276 (by decide) baseBL).map Fin.val).toArray := by
  refine CFSG.KS.Asch54.co3_sep (fun j hj => genB_mem (pairBS_size ▸ hj)) ?_
  rw [baseB_eq]
  decide

theorem chainA : rawChainOK 276 (pairAS.extract 0 17) pairAS
    ((co3FinList 276 (by decide) baseAL).map Fin.val).toArray (wordsArr 17 17 dNil) 4 = true :=
  rawChainTK_sound bindsA ch75337a.head ch75337a.tl ch75337a.hst sepA ch75337a.hs (by norm_num)

theorem chainB : rawChainOK 276 (pairBS.extract 0 18) pairBS
    ((co3FinList 276 (by decide) baseBL).map Fin.val).toArray (wordsArr 18 18 dNil) 4 = true :=
  rawChainTK_sound bindsB ch75337b.head ch75337b.tl ch75337b.hst sepB ch75337b.hs (by norm_num)

theorem card_A : Nat.card pairA = 3072 := by
  have hA := chainArrays_ofArrays (n := 276) (hn := by decide) (S := pairAS) (k := 17)
    (hk := pairAS_size.ge) (base := co3FinList 276 (by decide) baseAL) (hb := by decide)
    (W := wordsArr 17 17 dNil) (chainCheckFacts chainA).strong_inv
  have h := card_originalSubgroup_of_chainOK hA (by norm_num) chainA
  rw [CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup,
    rawOrbitSizesTK_sound bindsA ch75337a.head ch75337a.tl, orbA] at h
  rw [pairA, h]
  rfl

theorem card_B : Nat.card pairB = 27648 := by
  have hB := chainArrays_ofArrays (n := 276) (hn := by decide) (S := pairBS) (k := 18)
    (hk := pairBS_size.ge) (base := co3FinList 276 (by decide) baseBL) (hb := by decide)
    (W := wordsArr 18 18 dNil) (chainCheckFacts chainB).strong_inv
  have h := card_originalSubgroup_of_chainOK hB (by norm_num) chainB
  rw [CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup,
    rawOrbitSizesTK_sound bindsB ch75337b.head ch75337b.tl, orbB] at h
  rw [pairB, h]
  rfl

theorem pairA_le_P : pairA ≤ co3P := by
  rw [pairA, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact genA_mem hj

theorem pairB_le_P : pairB ≤ co3P := by
  rw [pairB, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact genB_mem hj

theorem T_le_A : co3T ≤ pairA := by
  rw [co3T_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine Subgroup.subset_closure ⟨k, by omega, ?_⟩
  rw [pairAS_lo k.2]
  rfl

theorem T_le_B : co3T ≤ pairB := by
  rw [co3T_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine Subgroup.subset_closure ⟨k, by omega, ?_⟩
  rw [pairBS_lo k.2]
  rfl

def SQ : Array (Array ℕ) := pairAArrs ++ pairBArrs

theorem SQ_size : SQ.size = 19 := by rw [SQ, Array.size_append, pairAArrs_size, pairBArrs_size]

theorem SQ_get {j : ℕ} (hj : j < 19) : SQ[j]! = unpack 276 9 (PQ j) := by
  rcases Nat.lt_or_ge j 9 with h | h
  · rw [SQ, getElem!_append_left (by rw [pairAArrs_size]; exact h), aArr_get h, PQ_lo h,
      bq (Orb.allN_iff.1 lnA j h), Nat.add_eq, Nat.zero_add]
  · rw [SQ, getElem!_append_right (by rw [pairAArrs_size]; exact h)
      (by rw [pairAArrs_size, pairBArrs_size]; exact hj), pairAArrs_size, bArr_get (by omega),
      PQ_hi h]
    have e := bq (Orb.allN_iff.1 lnB (j - 9) (by omega))
    rw [show 8 + (j - 9) = j - 1 by omega, Nat.add_eq, show 9 + (j - 9) = j by omega] at e
    rw [e, show 9 + (j - 9) = j by omega]

theorem SQ_mem {j : ℕ} (hj : j < 19) : permOfArr 276 SQ[j]! ∈ pairA ⊔ pairB := by
  rcases Nat.lt_or_ge j 9 with h | h
  · refine le_sup_left (a := pairA) (Subgroup.subset_closure ⟨j + 8, by omega, ?_⟩)
    rw [pairAS_hi (by omega) (by omega), SQ, getElem!_append_left (by rw [pairAArrs_size]; exact h),
      show j + 8 - 8 = j by omega]
  · refine le_sup_right (a := pairA) (Subgroup.subset_closure ⟨j - 1, by omega, ?_⟩)
    rw [pairBS_hi (by omega) (by omega), SQ, getElem!_append_right (by rw [pairAArrs_size]; exact h)
      (by rw [pairAArrs_size, pairBArrs_size]; exact hj), pairAArrs_size,
      show j - 1 - 8 = j - 9 by omega]

theorem gen_mem {k : ℕ} (hk : k < 2) {wd : List ℤ}
    (h : CFSG.KS.Prim.wordEqK 276 9 (mask 9) (pidn 276 9) PQ PQI 19 wd (Co3C.S k) = true) :
    co3GenPerm k ∈ pairA ⊔ pairB := by
  obtain ⟨e, hl⟩ := CFSG.KS.Prim.wordEqK_sound ⟨SQ_size, fun j hj => SQ_get hj⟩ permQ h
  have hrep : ∀ j < 19, Rep 276 SQ[j]! (permOfArr 276 SQ[j]!) := by
    intro j hj
    have hr := (rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 permQ j hj))).1
    rwa [← SQ_get hj] at hr
  have hr := rep_wordA (gs := fun h => permOfArr 276 SQ[h]!) (j := 19) hrep
    (fun h hh => by
      rw [Orb.rawInvs_get (by rw [SQ_size]; exact hh)]
      exact CFSG.KS.Raw.rep_invCand (hrep h hh)) wd hl
  rw [e] at hr
  have hk' : Orb.PRep 276 9 (Co3C.S k) (permOfArr 276 co3ChainArrs[k]!) :=
    (Orb.prep_PS Co3C.binds Co3C.perm (j := k) (by omega)).1
  have hg := Rep.unique (Orb.rep_unpack hk') hr
  change permOfArr 276 co3ChainArrs[k]! ∈ _
  rw [hg]
  refine (Subgroup.closure_le _).2 ?_ (CFSG.EvenSporadicStandard.Solomon78.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact SQ_mem h.2

theorem P_le_sup : co3P ≤ pairA ⊔ pairB := by
  rw [co3P_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  match k with
  | ⟨0, _⟩ => exact gen_mem (by norm_num) wordA0
  | ⟨1, _⟩ => exact gen_mem (by norm_num) wordA1

end CertificateChecks.Batch75337

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Co3 CFSG.LocalAnalysis.WeakClosure81.SporCo3 in
theorem certificate75337 : pairA ≤ co3P ∧ pairB ≤ co3P ∧ co3T ≤ pairA ∧ co3T ≤ pairB ∧
    Nat.card pairA = 3072 ∧ Nat.card pairB = 27648 ∧ co3P ≤ pairA ⊔ pairB :=
  ⟨CertificateChecks.Batch75337.pairA_le_P, CertificateChecks.Batch75337.pairB_le_P, CertificateChecks.Batch75337.T_le_A, CertificateChecks.Batch75337.T_le_B,
    CertificateChecks.Batch75337.card_A, CertificateChecks.Batch75337.card_B, CertificateChecks.Batch75337.P_le_sup⟩

end Certificates
