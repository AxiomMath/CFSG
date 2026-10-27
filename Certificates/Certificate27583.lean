module

public import Certificates.Data.TitsAschbacherE32Cent
public import Certificates.Kernel.EvenBN.K27583
public import CFSG.Certificates.Kernel.EvenBN.BaseTwSound
public import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27583

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32

@[expose] noncomputable def pF (h : Array Nat) : Bool :=
  (!commF h || (FL.map (unpack 1755 11)).any (eqA 1755 h)) &&
    !commF (compA 1755 h CFSG.Quasithin.titsPiArr)

theorem all5_of_nil {L : Array Level} {p : Array Nat → Bool}
    (h : survivors5 1755 L (fun a => !p a) = []) : all5 1755 L p = true := by
  unfold all5
  refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => allLt_iff.2 fun c hc =>
    allLt_iff.2 fun d hd => allLt_iff.2 fun e he => ?_
  cases hq : p (prod5 1755 L a b c d e)
  · have hmem : prod5 1755 L a b c d e ∈ survivors5 1755 L (fun a => !p a) := by
      simp only [survivors5, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range]
      exact ⟨a, ha, b, hb, c, hc, d, hd, ⟨e, he, rfl⟩, by simp [hq]⟩
    rw [h] at hmem
    exact absurd hmem List.not_mem_nil
  · rfl

theorem sH {Y : Nat} (cY : C Y)
    (h : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 Y = true) :
    siftA 1755 (rawLevels 1755 titsHArrs (baseArr 1755 titsHBase)) (baseArr 1755 titsHBase) 0
      (unpack 1755 11 Y) = true :=
  siftK_soundR bindsH permH TitsH.hl rfl (hi_of cY) (range_of_canonK cY) h

theorem rep_of {Y : Nat} (cY : C Y)
    (h : siftA 1755 (rawLevels 1755 titsHArrs (baseArr 1755 titsHBase)) (baseArr 1755 titsHBase) 0
      (unpack 1755 11 Y) = true) : ∃ γ, Rep 1755 (unpack 1755 11 Y) γ := by
  obtain ⟨-, -, -, r⟩ := canonK_facts cY
  exact rep_of_siftA bindsH permH TitsH.hl 5 0 rfl _ (fun i hi => by rw [unpack_getT hi]; exact r i hi) h

theorem tw_eq {X P V W : Array Nat} {σ p ν ν' : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ)
    (hP : Rep 1755 P p) (hV : Rep 1755 V ν) (hW : Rep 1755 W ν')
    (hrel : compA 1755 W P = compA 1755 P V) :
    commA (compA 1755 X P) V = eqA 1755 (compA 1755 X W) (compA 1755 V X) := by
  have hPV := rep_compA hP hV
  rw [← hrel] at hPV
  have e : ν' * p = p * ν := Rep.unique (rep_compA hW hP) hPV
  unfold commA
  rw [Bool.eq_iff_iff, eqA_iff (rep_compA (rep_compA hX hP) hV) (rep_compA hV (rep_compA hX hP)),
    eqA_iff (rep_compA hX hW) (rep_compA hV hX)]
  constructor
  · intro h
    have h' : σ * ν' * p = ν * σ * p := by rw [mul_assoc, e, ← mul_assoc, h, mul_assoc]
    exact mul_right_cancel h'
  · intro h
    rw [mul_assoc, ← e, ← mul_assoc, h, mul_assoc]

theorem pc_eq : Agrees TitsH.LR TitsH.TR
    (fun t0 t1 t2 t3 t4 => !CertificateChecks.KernelEvenBN.PC t0 t1 t2 t3 t4)
    (fun a => !pF a) := fun t0 t1 t2 t3 t4 htr => by
  obtain ⟨k0, k1, k2, k3, k4⟩ := canOf canTRH htr
  have rX : ∃ σ, Rep 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) σ := by
    obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
    exact ⟨_, (tr5_rep bindsH permH TitsH.hl h0 h1 h2 h3 h4).1⟩
  obtain ⟨σ, hσ⟩ := rX
  obtain ⟨hp1, -⟩ := rep_permOfArr (invEqK_sound (r := PiI) piPI).2
  have kv := fun i (hi : i ∈ fIdx) => List.all_eq_true.1 vpK i hi
  have hlt : ∀ i ∈ fIdx, i < 13 := by decide
  have e1 : (fIdx.all fun i => baseComm TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (V i))) =
      commF (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) := by
    unfold commF
    refine all_congr_mem fun i hi => ?_
    have k := kv i hi
    simp only [Bool.and_eq_true] at k
    rw [vA_eq (hlt i hi), baseCommG_eq bindsH TitsH.head TitsH.hl (NS := 220) (CH := 8) (by norm_num)
      TitsH.hs ndH htr (cV (hlt i hi)) (sH (cV (hlt i hi)) k.1.1.1)]
  have e2 : (FL.any fun f => eqPts 1755 11 (mask 11) f t0 t1 t2 t3 t4) =
      (FL.map (unpack 1755 11)).any (eqA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) :=
    (any_mapU fArrs_eq.2 fun f cf => (eqPts_sound k0 k1 k2 k3 k4 cf).symm).symm
  have e3 : (fIdx.all fun i => baseTw TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (VP i)) (pgR (V i))) =
      commF (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
        CFSG.Quasithin.titsPiArr) := by
    unfold commF
    refine all_congr_mem fun i hi => ?_
    have k := kv i hi
    simp only [Bool.and_eq_true] at k
    obtain ⟨⟨⟨s1, s2⟩, c2⟩, b⟩ := k
    have cv := cV (hlt i hi)
    obtain ⟨ν, hν⟩ := rep_of cv (sH cv s1)
    obtain ⟨ν', hν'⟩ := rep_of c2 (sH c2 s2)
    have hrel : compA 1755 (unpack 1755 11 (VP i)) (unpack 1755 11 Pi) =
        compA 1755 (unpack 1755 11 Pi) (unpack 1755 11 (V i)) := by
      rw [cmpU c2 cPi, cmpU cPi cv, Nat.eq_of_beq_eq_true b]
    rw [baseTwG_eq bindsH TitsH.head TitsH.hl (NS := 220) (CH := 8) (by norm_num) TitsH.hs ndH htr
      c2 (sH c2 s2) cv (sH cv s1), vA_eq (hlt i hi), pi_eq, tw_eq hσ hp1 hν hν' hrel]
  unfold pF CertificateChecks.KernelEvenBN.PC
  dsimp only
  rw [e1, e2, e3, pi_eq]

theorem tits_e32_cent_check_0 : centFCheck () = true := by
  have h : all5 1755 titsHLevels pF = true := all5_of_nil
    (surv5K_soundCT (C := []) bindsH permH TitsH.hl pc_eq (by quickRfl) (by quickRfl) TitsCF.all)
  unfold centFCheck
  rw [fArrs_eq.1]
  exact h

end CertificateChecks.Batch27583

namespace Certificates

open CertificateChecks

theorem certificate27583 : Certificates.TitsAschbacherE32.centFCheck () = true := by
  exact CertificateChecks.Batch27583.tits_e32_cent_check_0

end Certificates
