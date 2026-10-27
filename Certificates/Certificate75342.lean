module

public import CFSG.Sporadic.Co2Cert.Cert
public import CFSG.Sporadic.Co2Schreier.Defs
import Certificates.Kernel.Asch54.Co2GenP
import Certificates.Kernel.Sporadic.Co2.Order
import Certificates.Kernel.SporSch.Co2M.FratG
import Certificates.Certificate2049
import Certificates.Certificate2060
import Certificates.Certificate3115
import Certificates.Certificate3117
import CFSG.Certificates.Kernel.Asch54.Co2Sound
import CFSG.Certificates.Kernel.Spor.RawTreeSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.SiftBKProof
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.NativeSchreierCard
import CFSG.Sporadic.Co2Schreier.Chains
import CFSG.Sporadic.Co2Cert.Order
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.InvariantMerge
import CFSG.Sporadic.HeldB.Common
import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

set_option maxRecDepth 400000

namespace CertificateChecks.Batch75342

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelSpor CertificateChecks.KernelAsch54
  CertificateChecks.KernelAsch54.Co2

noncomputable def SA : Array (Array ℕ) := Array.ofFn fun j : Fin 6 => unpack 2300 12 (ch75342a.S j)

noncomputable def SB : Array (Array ℕ) := Array.ofFn fun j : Fin 5 => unpack 2300 12 (ch75342b.S j)

noncomputable def pairA : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {g | ∃ i < 6, permOfArr 2300 SA[i]! = g}

noncomputable def pairB : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {g | ∃ i < 5, permOfArr 2300 SB[i]! = g}

theorem SA_size : SA.size = 6 := Array.size_ofFn

theorem SB_size : SB.size = 5 := Array.size_ofFn

theorem SA_get {j : ℕ} (hj : j < 6) : SA[j]! = unpack 2300 12 (ch75342a.S j) := by
  rw [getElem!_pos SA j (by rw [SA_size]; exact hj)]
  exact Array.getElem_ofFn ..

theorem SB_get {j : ℕ} (hj : j < 5) : SB[j]! = unpack 2300 12 (ch75342b.S j) := by
  rw [getElem!_pos SB j (by rw [SB_size]; exact hj)]
  exact Array.getElem_ofFn ..

theorem closureA : Subgroup.closure {g | ∃ j < SA.size, permOfArr 2300 SA[j]! = g} = pairA := by
  rw [SA_size, pairA]

theorem closureB : Subgroup.closure {g | ∃ j < SB.size, permOfArr 2300 SB[j]! = g} = pairB := by
  rw [SB_size, pairB]

def baseAL : List ℕ := [29, 0, 3, 4, 5, 2, 1]

def baseBL : List ℕ := [29, 2, 3, 0, 5, 4, 1]

theorem baseA_eq : ((co3FinList 2300 (by decide) baseAL).map Fin.val).toArray =
    #[29, 0, 3, 4, 5, 2, 1] := by decide

theorem baseB_eq : ((co3FinList 2300 (by decide) baseBL).map Fin.val).toArray =
    #[29, 2, 3, 0, 5, 4, 1] := by decide

theorem bq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem bindsA : Binds 2300 12 ch75342a.S 6 7 ch75342a.BP SA
    ((co3FinList 2300 (by decide) baseAL).map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, SA_size, fun j hj => SA_get hj,
    by rw [baseA_eq]; rfl, fun t ht => ?_⟩
  rw [baseA_eq]
  exact bq (Orb.allN_iff.1 bgetA t ht)

theorem bindsB : Binds 2300 12 ch75342b.S 5 7 ch75342b.BP SB
    ((co3FinList 2300 (by decide) baseBL).map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, SB_size, fun j hj => SB_get hj,
    by rw [baseB_eq]; rfl, fun t ht => ?_⟩
  rw [baseB_eq]
  exact bq (Orb.allN_iff.1 bgetB t ht)

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_P_of {G : ℕ} {x : Equiv.Perm (Fin 2300)} (hx : Orb.PRep 2300 12 G x)
    (h : inPK G = true) : x ∈ co2P := by
  have hs := (and3 h).2.2
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (Orb.rep_unpack hx)).1 (siftK_sound Co2A.binds Co2A.perm Co2A.hl rfl (and3 h).2.1 hs)

theorem genA_mem {j : ℕ} (hj : j < 6) : permOfArr 2300 SA[j]! ∈ co2P :=
  mem_P_of (Orb.prep_PS bindsA (Orb.head_facts ch75342a.head).1 hj).1
    (Orb.allN_iff.1 genPA j hj)

theorem genB_mem {j : ℕ} (hj : j < 5) : permOfArr 2300 SB[j]! ∈ co2P :=
  mem_P_of (Orb.prep_PS bindsB (Orb.head_facts ch75342b.head).1 hj).1
    (Orb.allN_iff.1 genPB j hj)

theorem hbA : ∀ i < co2BaseArr.size, ∃ t < (((co3FinList 2300 (by decide) baseAL).map
    Fin.val).toArray).size, (((co3FinList 2300 (by decide) baseAL).map Fin.val).toArray)[t]! =
    co2BaseArr[i]! := by
  rw [baseA_eq, co2BaseArr_eq]
  decide

theorem hbB : ∀ i < co2BaseArr.size, ∃ t < (((co3FinList 2300 (by decide) baseBL).map
    Fin.val).toArray).size, (((co3FinList 2300 (by decide) baseBL).map Fin.val).toArray)[t]! =
    co2BaseArr[i]! := by
  rw [baseB_eq, co2BaseArr_eq]
  decide

theorem sepA : Sep 2300 SA ((co3FinList 2300 (by decide) baseAL).map Fin.val).toArray :=
  CFSG.KS.Asch54.co2_sep (fun j hj => genA_mem (SA_size ▸ hj)) hbA

theorem sepB : Sep 2300 SB ((co3FinList 2300 (by decide) baseBL).map Fin.val).toArray :=
  CFSG.KS.Asch54.co2_sep (fun j hj => genB_mem (SB_size ▸ hj)) hbB

theorem chainA : rawChainOK 2300 (SA.extract 0 6) SA
    ((co3FinList 2300 (by decide) baseAL).map Fin.val).toArray (wordsArr 6 6 Co2D.dNil) 4 = true :=
  rawChainTK_sound bindsA ch75342a.head ch75342a.tl ch75342a.hst sepA ch75342a.hs (by norm_num)

theorem chainB : rawChainOK 2300 (SB.extract 0 5) SB
    ((co3FinList 2300 (by decide) baseBL).map Fin.val).toArray (wordsArr 5 5 Co2D.dNil) 4 = true :=
  rawChainTK_sound bindsB ch75342b.head ch75342b.tl ch75342b.hst sepB ch75342b.hs (by norm_num)

theorem card_A : Nat.card pairA = 5505024 := by
  have hA := chainArrays_ofArrays (n := 2300) (hn := by decide) (S := SA) (k := 6)
    (hk := SA_size.ge) (base := co3FinList 2300 (by decide) baseAL) (hb := by decide)
    (W := wordsArr 6 6 Co2D.dNil) (chainCheckFacts chainA).strong_inv
  have h := card_originalSubgroup_of_chainOK hA (by norm_num) chainA
  rw [CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup,
    rawOrbitSizesTK_sound bindsA ch75342a.head ch75342a.tl, orbA] at h
  rw [pairA, h]
  rfl

theorem card_B : Nat.card pairB = 11796480 := by
  have hB := chainArrays_ofArrays (n := 2300) (hn := by decide) (S := SB) (k := 5)
    (hk := SB_size.ge) (base := co3FinList 2300 (by decide) baseBL) (hb := by decide)
    (W := wordsArr 5 5 Co2D.dNil) (chainCheckFacts chainB).strong_inv
  have h := card_originalSubgroup_of_chainOK hB (by norm_num) chainB
  rw [CFSG.ComponentClassification.J2Cover.ofArrays_originalSubgroup,
    rawOrbitSizesTK_sound bindsB ch75342b.head ch75342b.tl, orbB] at h
  rw [pairB, h]
  rfl

theorem pairA_le_P : pairA ≤ co2P := by
  rw [pairA, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact genA_mem hj

theorem pairB_le_P : pairB ≤ co2P := by
  rw [pairB, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact genB_mem hj

theorem mem_A_of {q : ℕ} {G : Equiv.Perm (Fin 2300)} (hq : Rep 2300 (unpack 2300 12 q) G)
    (hG : G ∈ co2P) (h : inA q = true) : G ∈ pairA := by
  rw [← closureA]
  exact siftBK_mem bindsA ch75342a.head ch75342a.tl ch75342a.hst
    (fun j hj => genA_mem hj) (fun G hG hfix => CFSG.KS.Asch54.co2_fix hbA hG hfix) hq hG h

theorem mem_B_of {q : ℕ} {G : Equiv.Perm (Fin 2300)} (hq : Rep 2300 (unpack 2300 12 q) G)
    (hG : G ∈ co2P) (h : inB q = true) : G ∈ pairB := by
  rw [← closureB]
  exact siftBK_mem bindsB ch75342b.head ch75342b.tl ch75342b.hst
    (fun j hj => genB_mem hj) (fun G hG hfix => CFSG.KS.Asch54.co2_fix hbB hG hfix) hq hG h

theorem rep_s {j : ℕ} (hj : j < 15) :
    Rep 2300 (unpack 2300 12 (KernelSporSch.Co2LS.S j)) (sTuple.getD j 1) := by
  rw [← KernelSporSch.Co2M.s_eq hj]
  exact repTuple_s.rep (by rw [sTuple_length]; exact hj)

theorem mem_s {g : Equiv.Perm (Fin 2300)} (hg : g ∈ sTuple) :
    ∃ j < 15, sTuple.getD j 1 = g := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact ⟨j, by rwa [sTuple_length] at hj, List.getD_eq_getElem _ _ hj⟩

theorem S_le_A : locS ≤ pairA := by
  rw [locS, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, hjg⟩ := mem_s hg
  have hm : sTuple.getD j 1 ∈ sTuple := by
    rw [hjg]
    exact hg
  rw [SetLike.mem_coe, ← hjg]
  exact mem_A_of (rep_s hj) (locS_le_P (Subgroup.subset_closure hm)) (Orb.allN_iff.1 memSA j hj)

theorem S_le_B : locS ≤ pairB := by
  rw [locS, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, hjg⟩ := mem_s hg
  have hm : sTuple.getD j 1 ∈ sTuple := by
    rw [hjg]
    exact hg
  rw [SetLike.mem_coe, ← hjg]
  exact mem_B_of (rep_s hj) (locS_le_P (Subgroup.subset_closure hm)) (Orb.allN_iff.1 memSB j hj)

noncomputable def SL : Array (Array ℕ) := Array.ofFn fun j : Fin 29 => unpack 2300 12 (L j)

theorem SL_size : SL.size = 29 := Array.size_ofFn

theorem SL_get {j : ℕ} (hj : j < 29) : SL[j]! = unpack 2300 12 (L j) := by
  rw [getElem!_pos SL j (by rw [SL_size]; exact hj)]
  exact Array.getElem_ofFn ..

theorem rep_L {j : ℕ} (hj : j < 29) : Rep 2300 SL[j]! (permOfArr 2300 SL[j]!) := by
  have hr := (rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 permL j hj))).1
  rwa [← SL_get hj] at hr

theorem SL_mem {j : ℕ} (hj : j < 29) : permOfArr 2300 SL[j]! ∈ pairA ⊔ pairB := by
  have hr : Rep 2300 (unpack 2300 12 (L j)) (permOfArr 2300 SL[j]!) :=
    (congrArg (fun t => Rep 2300 t (permOfArr 2300 SL[j]!)) (SL_get hj)).mp (rep_L hj)
  have hP : permOfArr 2300 SL[j]! ∈ co2P :=
    mem_P_of (Orb.prep_of_rep hr) (Orb.allN_iff.1 inP j hj)
  rcases Nat.lt_or_ge j 14 with h | h
  · exact le_sup_left (a := pairA) (mem_A_of hr hP (Orb.allN_iff.1 memA j h))
  · have hs := Orb.allN_iff.1 memB (j - 14) (by omega)
    rw [Nat.add_eq, show 14 + (j - 14) = j by omega] at hs
    exact le_sup_right (a := pairA) (mem_B_of hr hP hs)

theorem gen_mem {k : ℕ} (hk : k < 2) {wd : List ℤ}
    (h : CFSG.KS.Prim.wordEqK 2300 12 (mask 12) (pidn 2300 12) L LI 29 wd (Co2A.S k) = true) :
    co2Gen k ∈ pairA ⊔ pairB := by
  obtain ⟨e, hl⟩ := CFSG.KS.Prim.wordEqK_sound ⟨SL_size, fun j hj => SL_get hj⟩ permL h
  have hr := rep_wordA (gs := fun h => permOfArr 2300 SL[h]!) (j := 29) (fun h hh => rep_L hh)
    (fun h hh => by
      rw [Orb.rawInvs_get (by rw [SL_size]; exact hh)]
      exact CFSG.KS.Raw.rep_invCand (rep_L hh)) wd hl
  rw [e] at hr
  have hk' : Orb.PRep 2300 12 (Co2A.S k) (permOfArr 2300 co2StrongArrs[k]!) :=
    (Orb.prep_PS Co2A.binds Co2A.perm (j := k) (by omega)).1
  have hg := Rep.unique (Orb.rep_unpack hk') hr
  rw [co2Gen, ← KernelSpor.Co2Order.sA k hk, hg]
  refine (Subgroup.closure_le _).2 ?_ (CFSG.EvenSporadicStandard.Solomon78.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact SL_mem h.2

theorem P_le_sup : co2P ≤ pairA ⊔ pairB := by
  rw [co2P, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact gen_mem (by norm_num) wordA0
  · exact gen_mem (by norm_num) wordA1

end CertificateChecks.Batch75342

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier in
theorem certificate75342 : ∃ A₀ B₀ : Subgroup (Equiv.Perm (Fin 2300)), A₀ ≤ co2P ∧ B₀ ≤ co2P ∧ locS ≤ A₀ ∧
    locS ≤ B₀ ∧ Nat.card A₀ = 5505024 ∧ Nat.card B₀ = 11796480 ∧ co2P ≤ A₀ ⊔ B₀ :=
  ⟨CertificateChecks.Batch75342.pairA, CertificateChecks.Batch75342.pairB, CertificateChecks.Batch75342.pairA_le_P, CertificateChecks.Batch75342.pairB_le_P,
    CertificateChecks.Batch75342.S_le_A, CertificateChecks.Batch75342.S_le_B, CertificateChecks.Batch75342.card_A, CertificateChecks.Batch75342.card_B,
    CertificateChecks.Batch75342.P_le_sup⟩

end Certificates

end
