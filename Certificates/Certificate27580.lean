module

public import Certificates.Data.TitsAschbacherE32
public import Certificates.Kernel.EvenBN.K27580A
public import Certificates.Kernel.EvenBN.K27580P
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27580

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelEvenBN
open CertificateChecks.KernelEvenBN.E32
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32 Certificates.TitsAschbacherSecFour

theorem eqA_self (x : Array Nat) : eqA 1755 x x = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem partA (L : Array Level) (p : Array Nat → Bool) :
    all5 1755 L (fun y => !p y || (survivors5 1755 L p).any (eqA 1755 y)) = true := by
  unfold all5
  refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => allLt_iff.2 fun c hc =>
    allLt_iff.2 fun d hd => allLt_iff.2 fun e he => ?_
  beta_reduce
  cases hq : p (prod5 1755 L a b c d e)
  · rfl
  · have hmem : prod5 1755 L a b c d e ∈ survivors5 1755 L p := by
      simp only [survivors5, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range]
      exact ⟨a, ha, b, hb, c, hc, d, hd, ⟨e, he, rfl⟩, hq⟩
    rw [Bool.not_true, Bool.false_or]
    exact List.any_eq_true.2 ⟨_, hmem, eqA_self _⟩

theorem ndS : (baseArr 1755 titsSBase).toList.Nodup := by decide

theorem canTRS : allN 5 (fun i => allN (rcnt (TitsS.LR i)) (fun a =>
    canonK 1755 11 (mask 11) (1755 * 11) (trAt 1755 (1755 * 11) TitsS.LR TitsS.TR i a))) = true := by
  quickRfl

theorem agrI : Agrees TitsS.LR TitsS.TR invK isInvol := fun t0 t1 t2 t3 t4 htr => by
  obtain ⟨k0, k1, k2, k3, k4⟩ := TitsInv.canOf canTRS htr
  unfold invK isInvol
  rw [sqPts_sound k0 k1 k2 k3 k4, eqPts_sound k0 k1 k2 k3 k4 TitsCentral.canId, TitsCentral.id_eq]

theorem sInvs_eq : sInvs () = SI.L.map (unpack 1755 11) := by
  have h := surv5K_soundCT (C := SI.C) bindsS permS TitsS.hl agrI mI aI SIA.all
  rw [zipK_beq_map zI, List.map_map]
  exact h

theorem lfacts {A : Nat} (hA : A ∈ SI.L) : C A ∧ sS A = true := by
  have h := List.all_eq_true.1 lK A hA
  simp only [Bool.and_eq_true] at h
  exact h

theorem sSs {A : Nat} (cA : C A) (h : sS A = true) :
    siftA 1755 (rawLevels 1755 titsSArrs (baseArr 1755 titsSBase)) (baseArr 1755 titsSBase) 0
      (unpack 1755 11 A) = true :=
  siftK_soundR bindsS permS TitsS.hl rfl (hi_of cA) (range_of_canonK cA) h

theorem inJ_eq {A : Nat} (cA : C A) : inJ (unpack 1755 11 A) = sJ A :=
  CFSG.KS.Raw.siftK_eq bindsJ permJ TitsJ.hl rfl (hi_of cA) (range_of_canonK cA)

theorem repS {A : Nat} (cA : C A) (sA : sS A = true) : ∃ σ, Rep 1755 (unpack 1755 11 A) σ := by
  obtain ⟨-, -, -, r⟩ := canonK_facts cA
  exact rep_of_siftA bindsS permS TitsS.hl 5 0 rfl _ (fun i hi => by rw [unpack_getT hi]; exact r i hi)
    (sSs cA sA)

theorem commP_eq {A B : Nat} (cA : C A) (sA : sS A = true) (cB : C B) (sB : sS B = true) :
    commP A B = commA (unpack 1755 11 A) (unpack 1755 11 B) := by
  obtain ⟨G, hmem, hsep⟩ := chain_group bindsS TitsS.head TitsS.hl (NS := 220) (CH := 8)
    (by norm_num) TitsS.hs ndS
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels bindsS TitsS.hl
  obtain ⟨σ, rA⟩ := repS cA sA
  obtain ⟨τ, rB⟩ := repS cB sB
  exact baseComm_of_sep hsep hbl (fun t ht => bindsS.2.2.2.2.2.2 t ht) rA rB
    ((hmem _ _ rA).1 (sSs cA sA)) ((hmem _ _ rB).1 (sSs cB sB))
    (fun i hi => by rw [pgR_eq, unpack_getT hi]) (fun i hi => by rw [pgR_eq, unpack_getT hi])

theorem piv_eq {A : Nat} (hA : A ∈ SI.L) :
    pivotOK (eArrs ()) (SI.L.map (unpack 1755 11)) (xkData.map (xkSet (eArrs ()) (fArrs ())))
      (unpack 1755 11 A) = pivK A := by
  obtain ⟨cA, sA⟩ := lfacts hA
  have hE : (eArrs ()).any (eqA 1755 (unpack 1755 11 A)) = EL.any (Nat.beq A) := by
    rw [eArrs_eq.1]
    exact any_mapU eArrs_eq.2 fun x cx => eqU cA cx
  have hF : ∀ B ∈ SI.L, (commA (unpack 1755 11 A) (unpack 1755 11 B) &&
      (!inJ (unpack 1755 11 A) || inJ (unpack 1755 11 B))) = (commP A B && (!sJ A || sJ B)) :=
    fun B hB => by
      obtain ⟨cB, sB⟩ := lfacts hB
      rw [commP_eq cA sA cB sB, inJ_eq cA, inJ_eq cB]
  have hom : (SI.L.map (unpack 1755 11)).filter (fun b => commA (unpack 1755 11 A) b &&
      (!inJ (unpack 1755 11 A) || inJ b)) =
      (SI.L.filter fun B => commP A B && (!sJ A || sJ B)).map (unpack 1755 11) := by
    rw [List.filter_map]
    exact congrArg (List.map (unpack 1755 11)) (List.filter_congr fun B hB => hF B hB)
  have hX : ∀ e ∈ xkData, ((SI.L.filter fun B => commP A B && (!sJ A || sJ B)).map
      (unpack 1755 11)).all (fun b => (xkSet (EL.map (unpack 1755 11)) (FL.map (unpack 1755 11))
        e).any (eqA 1755 b)) =
      (SI.L.filter fun B => commP A B && (!sJ A || sJ B)).all fun B => (xkL e).any (Nat.beq B) :=
    fun e he => by
      rw [(xkSet_eq he).1]
      exact all_mapU (fun x hx => (lfacts (List.mem_of_mem_filter hx)).1) fun x cx =>
        any_mapU (xkSet_eq he).2 fun y cy => eqU cx cy
  unfold pivotOK pivK XL
  simp only [hE]
  rw [hom, eArrs_eq.1, fArrs_eq.1, List.any_map, List.any_map]
  exact congrArg (EL.any (Nat.beq A) || ·) (any_congr_mem fun e he => hX e he)

theorem pivAll : SI.L.all pivK = true := by
  rw [← List.take_append_drop 36 SI.L, List.all_append, p0, Bool.true_and,
    ← List.take_append_drop 36 (SI.L.drop 36), List.all_append, p1, Bool.true_and]
  simp only [List.drop_drop]
  rw [← List.take_append_drop 36 (SI.L.drop 72), List.all_append, p2, Bool.true_and]
  simp only [List.drop_drop]
  exact p3

theorem partB : xkData.all (fun e => (if e.1 then nLetters e.2.2 else hLetters e.2.2) &&
    isInvA 1755 (xkConj e) (invCand 1755 (xkConj e))) = true := by
  refine List.all_eq_true.2 fun e he => ?_
  have hl : (if e.1 then nLetters e.2.2 else hLetters e.2.2) = true := by revert e; decide
  obtain ⟨hc, -⟩ := xkC_eq he
  have k := List.all_eq_true.1 xkK e he
  simp only [Bool.and_eq_true] at k
  rw [hl, hc, invCand_unpack k.1, (invEqK_sound k.1).2]
  rfl

theorem e32_ok : e32Check () = true := by
  have hC : (sInvs ()).all (pivotOK (eArrs ()) (sInvs ())
      (xkData.map (xkSet (eArrs ()) (fArrs ())))) = true := by
    rw [sInvs_eq, List.all_map, ← pivAll]
    exact all_congr_mem fun A hA => piv_eq hA
  have hA : (all5 1755 titsSLevels fun y => !isInvol y || (sInvs ()).any (eqA 1755 y)) = true :=
    partA titsSLevels isInvol
  unfold e32Check
  simp only []
  rw [hA, partB, hC]
  rfl

end CertificateChecks.Batch27580

namespace Certificates

open CertificateChecks

theorem certificate27580 : Certificates.TitsAschbacherE32.e32Check () = true := CertificateChecks.Batch27580.e32_ok

end Certificates
