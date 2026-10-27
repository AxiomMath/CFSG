module

public import Certificates.Kernel.Census.Suz.Bind
public import Certificates.Kernel.Census.Suz.T
public import Certificates.Kernel.Census.Suz.Inv
public import Certificates.Kernel.Census.Suz.Tab
public import Certificates.Kernel.Census.Suz.E0
public import Certificates.Kernel.Census.Suz.E1
public import Certificates.Kernel.Census.Suz.E2
public import Certificates.Kernel.Census.Suz.E3
public import Certificates.Kernel.Census.Suz.E4
public import Certificates.Kernel.Census.Suz.E5
public import Certificates.Kernel.Census.Suz.E6
public import Certificates.Kernel.Census.Suz.E7
public import Certificates.Kernel.Census.Suz.E8
public import Certificates.Kernel.Census.Suz.E9
public import Certificates.Kernel.Census.Suz.E10
public import Certificates.Kernel.Census.Suz.NII0
public import Certificates.Kernel.Census.Suz.NII1
public import Certificates.Kernel.Census.Suz.NII2
public import Certificates.Kernel.Census.Suz.NII3
public import Certificates.Kernel.Census.Suz.NII4
public import Certificates.Kernel.Census.Suz.NII5
public import Certificates.Kernel.Census.Suz.NII6
public import Certificates.Kernel.Census.Suz.NII7
public import Certificates.Kernel.Census.Suz.NII8
public import Certificates.Kernel.Census.Suz.NII9
public import Certificates.Kernel.Census.Suz.NII10
public import Certificates.Kernel.Census.Suz.NII11
public import Certificates.Kernel.Census.Suz.NII12
public import Certificates.Kernel.Census.Suz.NII13
public import Certificates.Kernel.Census.Suz.NExc0
public import Certificates.Kernel.Census.Suz.NExc1
public import Certificates.Kernel.Census.Suz.NExc2
public import Certificates.Kernel.Census.Suz.NExc3
public import Certificates.Kernel.Census.Suz.NExc4
public import Certificates.Kernel.Census.Suz.NExc5
public import Certificates.Kernel.Census.Suz.NExc6
public import Certificates.Kernel.Census.Suz.NExc7
public import Certificates.Kernel.Census.Suz.NExc8
public import Certificates.Kernel.Census.Suz.NExc9
public import Certificates.Kernel.Census.Suz.NExc10
public import Certificates.Kernel.Census.Suz.NExc11
public import Certificates.Kernel.Census.Suz.NExc12
public import Certificates.Kernel.Census.Suz.NExc13
public import CFSG.Certificates.Kernel.Census.ConjProof
public import CFSG.Certificates.Kernel.Census.ConjSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.DataII
import all Certificates.Kernel.Census.Suz.DataExc
import all Certificates.Kernel.Census.Suz.Sift
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Suz
open CFSG.ComponentClassification.RankTwoSporadic.Cert CertificateChecks.KernelSpor

set_option maxRecDepth 1000000

#kc_forall_chunks eb_c (fun j => ebF j = true) 44 CertificateChecks.KernelCensus.Suz.kE 1

#kc_forall_chunks nII_c (fun k => (List.range' (7 * k) 7).all (nodeQ true conjII #[]) = true) 23
  CertificateChecks.KernelCensus.Suz.kNII 7

#kc_forall_chunks nExc_c
  (fun k => (List.range' (7 * k) 7).all (nodeQ false conjExc suzE0P) = true) 23
  CertificateChecks.KernelCensus.Suz.kNExc 7

theorem inv_ok : pinvOK 1782 11 suzXs suzUs suzIm suzWt = true := by
  have hw : pinvRest 1782 11 suzXs 0 suzIm suzWt = some (suzIm.drop 911) := by
    unfold suzWt
    simp only [List.append_assoc]
    rw [pinvRest_append_of (L := 4096) (m' := 4096) (by decide +kernel) (by norm_num) kW0,
      pinvRest_append_of (L := 4096) (m' := 8192) (by decide +kernel) (by norm_num) kW1,
      pinvRest_append_of (L := 4096) (m' := 12288) (by decide +kernel) (by norm_num) kW2]
    exact kW3
  have hd : suzIm.drop 911 = [] := by decide +kernel
  have hu : (suzUs.toList.zip suzIm).all
      (fun ua => Nat.beq (ppcA 1782 11 suzXs ua.2) ua.1) = true :=
    zip_all_of_chunks (L := 160) (C := 6) (Nat.le_of_ble_eq_true (by quickRfl)) fun c hc => by
      interval_cases c
      exacts [kU0, kU1, kU2, kU3, kU4, kU5]
  have hl : Nat.beq suzIm.length suzUs.size = true := by quickRfl
  have hwl : Nat.beq suzWt.length (2 ^ suzXs.length) = true := by quickRfl
  unfold pinvOK
  rw [hw, hd, hl, hu, hwl]
  rfl

theorem tab_ok : ptabOK 1782 11 suzXs suzCm suzCs suzCi = true := by
  have hc : (suzCs.toList.zip suzCm).all
      (fun sm => Nat.beq (ppcA 1782 11 suzXs sm.2) sm.1) = true :=
    zip_all_of_chunks (L := 128) (C := 4) (Nat.le_of_ble_eq_true (by quickRfl)) fun c hc => by
      interval_cases c
      exacts [kC0, kC1, kC2, kC3]
  have h1 : Nat.beq suzCm.length suzCs.size = true := by quickRfl
  have h2 : Nat.beq suzCi.size suzCs.size = true := by quickRfl
  unfold ptabOK
  rw [h1, h2, hc, kCI]
  rfl

theorem roots_ok : (suzUs.toList.zip suzRoots).all
    (fun ur => prootOKC 1782 11 suzBases cNL suzCs suzCi ur.1 ur.2) = true :=
  zip_all_of_chunks (L := 256) (C := 4) (Nat.le_of_ble_eq_true (by quickRfl)) fun c hc => by
    interval_cases c
    exacts [kR0, kR1, kR2, kR3]

theorem eb_all : suzEB.all (fun b => entB b.1 b.2.1 b.2.2) = true := by
  refine List.all_eq_true.2 fun b hb => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have h44 : j < 44 := Nat.eq_of_beq_eq_true kEB ▸ hj
  have h := eb_c j h44
  unfold ebF at h
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h

theorem ents_ok {i : Nat} (hi : suzEL.any (fun t => t.1 == i) = true) :
    pentsOK 1782 11 suzBases cNL suzUs suzCs suzCi suzEnts[i]! i = true := by
  obtain ⟨t, ht, hti⟩ := List.any_eq_true.1 hi
  rw [beq_iff_eq] at hti
  subst hti
  have hk := List.all_eq_true.1 kEL t ht
  simp only [Bool.and_eq_true] at hk
  refine pentsOK_of_blocks (L := t.2.1) (C := t.2.2) hk.1 (Nat.le_of_ble_eq_true hk.2)
    fun c hc => ?_
  have hm : (t.1, c * t.2.1, t.2.1) ∈ suzEB :=
    List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩⟩
  exact List.all_eq_true.1 eb_all _ hm

theorem nodesQII : ∀ i < 167, nodeQ true conjII #[] i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 161 with h | h
  · have hk : i / 7 < 23 := by omega
    exact List.all_eq_true.1 (nII_c (i / 7) hk) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 kNII161 i (List.mem_range'_1.2 ⟨h, by omega⟩)

theorem nodesQExc : ∀ i < 167, nodeQ false conjExc suzE0P i = true := by
  intro i hi
  rcases Nat.lt_or_ge i 161 with h | h
  · have hk : i / 7 < 23 := by omega
    exact List.all_eq_true.1 (nExc_c (i / 7) hk) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 kNExc161 i (List.mem_range'_1.2 ⟨h, by omega⟩)

theorem nodes_okII : ∀ i < conjII.nodes.size, pnodeOKC 1782 11 suzPS inMP inMP inTP false
    true false conjII (pcN 1782 11 conjII.nodes) #[] i = true := by
  rw [cN_eq bases_eqII, Nat.eq_of_beq_eq_true kNSII]
  intro i hi
  refine pnodeOKC_of_q (nodesQII i hi) fun hm => ?_
  have he := List.all_eq_true.1 kELII i (List.mem_range.2 hi)
  rw [hm, Bool.false_or] at he
  rw [bases_eqII]
  exact ents_ok he

theorem nodes_okExc : ∀ i < conjExc.nodes.size, pnodeOKC 1782 11 suzPS inMP inMP inTP false
    false false conjExc (pcN 1782 11 conjExc.nodes) suzE0P i = true := by
  rw [cN_eq bases_eqExc, Nat.eq_of_beq_eq_true kNSExc]
  intro i hi
  refine pnodeOKC_of_q (nodesQExc i hi) fun hm => ?_
  have he := List.all_eq_true.1 kELExc i (List.mem_range.2 hi)
  rw [hm, Bool.false_or] at he
  rw [bases_eqExc]
  exact ents_ok he

theorem hin : ∀ P, canon1 1782 11 P = true → pvalid 1782 11 P = true →
    inMP P = suzInM (unpackP 1782 11 P) := fun _ hP hv => inM_eq hP hv

theorem hinW : ∀ P, canon1 1782 11 P = true → pvalid 1782 11 P = true →
    inTP P = suzInT (unpackP 1782 11 P) := fun _ hP hv => inT_eq hP hv kVV

theorem suz_okII : ∃ d : ConjDataP, suzCheckWII d = true := by
  have hR : (conjII.us.toList.zip conjII.roots).all (fun ur => prootOKC 1782 11
      (conjII.nodes.map NodeP.basis) (pcN 1782 11 conjII.nodes) conjII.cs conjII.ci
        ur.1 ur.2) = true := by
    rw [cN_eq bases_eqII, bases_eqII]
    exact roots_ok
  have hc := pconjCensus_sound_proved (ps := suzPS) (allowPW := false) (allowInX := true)
    (allowU := false) (e0 := #[]) (by norm_num) (by norm_num) (by norm_num) kCanonII
    (by quickRfl) hin hin hinW kPc inv_ok tab_ok kRl hR nodes_okII
  rw [Array.map_empty] at hc
  refine ⟨conjII, ?_⟩
  unfold suzCheckWII
  rw [hc, xs_ok _ rfl kG kVV kXV (Nat.eq_of_beq_eq_true kLen)]
  rfl

theorem suz_okExc : ∃ d : ConjDataP, suzCheckWExc suzE0 d = true := by
  have hR : (conjExc.us.toList.zip conjExc.roots).all (fun ur => prootOKC 1782 11
      (conjExc.nodes.map NodeP.basis) (pcN 1782 11 conjExc.nodes) conjExc.cs conjExc.ci
        ur.1 ur.2) = true := by
    rw [cN_eq bases_eqExc, bases_eqExc]
    exact roots_ok
  have hc := pconjCensus_sound_proved (ps := suzPS) (allowPW := false) (allowInX := false)
    (allowU := false) (e0 := suzE0P) (by norm_num) (by norm_num) (by norm_num) kCanonExc
    kE0P hin hin hinW kPc inv_ok tab_ok kRl hR nodes_okExc
  rw [suzE0_eq] at hc
  refine ⟨conjExc, ?_⟩
  unfold suzCheckWExc
  rw [hc, xs_ok _ rfl kG kVV kXV (Nat.eq_of_beq_eq_true kLen)]
  rfl

end CertificateChecks.KernelCensus.Suz

end
