module

public import Certificates.Data.TitsAschbacherNLocal
public import Certificates.Kernel.EvenBN.K27586K
public import Certificates.Kernel.EvenBN.K27586S
public import Certificates.Kernel.EvenBN.K27586R
public import Certificates.Kernel.EvenBN.K27586F
public import CFSG.Certificates.Kernel.EvenBN.BaseTwSound
public import CFSG.Certificates.Kernel.EvenBN.Sift0Sound
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.SporSch.Tits.Inv2266M
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27586

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN CertificateChecks.KernelEvenBN.NLoc
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32
open Certificates.TitsAschbacherNLocal Certificates.TitsAschbacherSecFour

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

theorem ndK : (baseArr 1755 titsKBase).toList.Nodup := by decide
theorem ndS : (baseArr 1755 titsSBase).toList.Nodup := by decide

theorem canTRS : allN 5 (fun i => allN (rcnt (TitsS.LR i)) (fun a =>
    canonK 1755 11 (mask 11) (1755 * 11) (trAt 1755 (1755 * 11) TitsS.LR TitsS.TR i a))) = true := by
  quickRfl

theorem sKs {X : Nat} (cX : C X) (h : sK X = true) :
    siftA 1755 (rawLevels 1755 titsKArrs (baseArr 1755 titsKBase)) (baseArr 1755 titsKBase) 0
      (unpack 1755 11 X) = true :=
  siftK_soundR bindsK permK TitsK.hl rfl (hi_of cX) (range_of_canonK cX) h

theorem repK {X : Nat} (cX : C X) (h : sK X = true) : ∃ γ, Rep 1755 (unpack 1755 11 X) γ := by
  obtain ⟨-, -, -, r⟩ := canonK_facts cX
  exact rep_of_siftA bindsK permK TitsK.hl 5 0 rfl _ (fun i hi => by rw [unpack_getT hi]; exact r i hi)
    (sKs cX h)

theorem jlt : ∀ i ∈ jL, i < 13 := by decide

theorem vq {i : Nat} (hi : i ∈ jL) : sK (V i) = true ∧ sK (VQ i) = true ∧ C (VQ i) ∧
    Nat.beq (pc (VQ i) Pi) (pc Pi (V i)) = true := by
  have h := List.all_eq_true.1 vqK i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem wq {j m : Nat} (hj : j ∈ jL) (hm : m ∈ uL) : sK (W m j) = true ∧ C (W m j) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 wK j hj) m hm
  simp only [Bool.and_eq_true] at h
  exact h

theorem ult : ∀ m ∈ uL, m < 32 := by decide

theorem cFL {m : Nat} (hm : m < 32) : C (FL.getD m 0) :=
  fArrs_eq.2 _ (getD_mem (by rw [FL_len]; exact hm))

theorem fA_eq {m : Nat} (hm : m < 32) : fA m = unpack 1755 11 (FL.getD m 0) := by
  unfold fA
  rw [fArrs_eq.1, getD_mapU (by rw [FL_len]; exact hm)]

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

theorem tw2_eq {X P V W Z : Array Nat} {σ p ν ν' ζ : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ)
    (hP : Rep 1755 P p) (hV : Rep 1755 V ν) (hW : Rep 1755 W ν') (hZ : Rep 1755 Z ζ)
    (hrel : compA 1755 W P = compA 1755 P V) :
    eqA 1755 (compA 1755 (compA 1755 X P) V) (compA 1755 Z (compA 1755 X P)) =
      eqA 1755 (compA 1755 X W) (compA 1755 Z X) := by
  have hPV := rep_compA hP hV
  rw [← hrel] at hPV
  have e : ν' * p = p * ν := Rep.unique (rep_compA hW hP) hPV
  rw [Bool.eq_iff_iff, eqA_iff (rep_compA (rep_compA hX hP) hV) (rep_compA hZ (rep_compA hX hP)),
    eqA_iff (rep_compA hX hW) (rep_compA hZ hX)]
  constructor
  · intro h
    have h' : σ * ν' * p = ζ * σ * p := by rw [mul_assoc, e, ← mul_assoc, h, mul_assoc]
    exact mul_right_cancel h'
  · intro h
    rw [mul_assoc, ← e, ← mul_assoc, h, mul_assoc]

section KPart

variable {t0 t1 t2 t3 t4 : Nat} (htr : IsTr5 TitsK.LR TitsK.TR t0 t1 t2 t3 t4)
include htr

theorem bc {i : Nat} (hi : i ∈ jL) :
    baseComm TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (V i)) =
      commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (vA i) := by
  rw [vA_eq (jlt i hi), baseCommG_eq bindsK TitsK.head TitsK.hl (NS := 220) (CH := 8) (by norm_num)
    TitsK.hs ndK htr (cV (jlt i hi)) (sKs (cV (jlt i hi)) (vq hi).1)]

theorem bt {j m : Nat} (hj : j ∈ jL) (hm : m ∈ uL) :
    baseTw TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (V j)) (pgR (W m j)) =
      eqA 1755 (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (vA j))
        (compA 1755 (compA 1755 (fA m) (vA j))
          (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) := by
  have cv := cV (jlt j hj)
  rw [baseTwG_eq bindsK TitsK.head TitsK.hl (NS := 220) (CH := 8) (by norm_num) TitsK.hs ndK htr
    cv (sKs cv (vq hj).1) (wq hj hm).2 (sKs (wq hj hm).2 (wq hj hm).1), vA_eq (jlt j hj),
    fA_eq (ult m hm), cmpU (cFL (ult m hm)) cv]
  rfl

theorem cT_eq : NLoc.cT (gptR t0 t1 t2 t3 t4) =
    cTest (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) := by
  unfold NLoc.cT cTest commInU11
  have e : ([10, 11, 12].all fun i => baseComm TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (V i))) =
      (commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (vA 10) &&
        commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (vA 11) &&
        commA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) (vA 12)) := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, bc htr (i := 10) (by decide),
      bc htr (i := 11) (by decide), bc htr (i := 12) (by decide), Bool.and_assoc]
  rw [e]
  congr 1
  exact all_congr_mem fun j hj => any_congr_mem fun m hm => bt htr hj hm

theorem repX : ∃ σ, Rep 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) σ := by
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  exact ⟨_, (tr5_rep bindsK permK TitsK.hl h0 h1 h2 h3 h4).1⟩

theorem cTP_eq : cTP (gptR t0 t1 t2 t3 t4) =
    cTest (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
      CFSG.Quasithin.titsPiArr) := by
  obtain ⟨σ, hσ⟩ := repX htr
  obtain ⟨hp1, -⟩ := rep_permOfArr (invEqK_sound (r := PiI) piP).2
  have hrel {i : Nat} (hi : i ∈ jL) : compA 1755 (unpack 1755 11 (VQ i)) (unpack 1755 11 Pi) =
      compA 1755 (unpack 1755 11 Pi) (unpack 1755 11 (V i)) := by
    rw [cmpU (vq hi).2.2.1 cPi, cmpU cPi (cV (jlt i hi))]
    exact congrArg (unpack 1755 11) (Nat.eq_of_beq_eq_true (vq hi).2.2.2)
  have tc {i : Nat} (hi : i ∈ jL) :
      baseTw TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (VQ i)) (pgR (V i)) =
        commA (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr) (vA i) := by
    have cv := cV (jlt i hi)
    obtain ⟨ν, hν⟩ := repK cv (vq hi).1
    obtain ⟨ν', hν'⟩ := repK (vq hi).2.2.1 (vq hi).2.1
    rw [baseTwG_eq bindsK TitsK.head TitsK.hl (NS := 220) (CH := 8) (by norm_num) TitsK.hs ndK htr
      (vq hi).2.2.1 (sKs (vq hi).2.2.1 (vq hi).2.1) cv (sKs cv (vq hi).1), vA_eq (jlt i hi), pi_eq,
      tw_eq hσ hp1 hν hν' (hrel hi)]
  have tt {j m : Nat} (hj : j ∈ jL) (hm : m ∈ uL) :
      baseTw TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (VQ j)) (pgR (W m j)) =
        eqA 1755 (compA 1755 (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr) (vA j)) (compA 1755 (compA 1755 (fA m) (vA j))
            (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
              CFSG.Quasithin.titsPiArr)) := by
    have cv := cV (jlt j hj)
    obtain ⟨ν, hν⟩ := repK cv (vq hj).1
    obtain ⟨ν', hν'⟩ := repK (vq hj).2.2.1 (vq hj).2.1
    obtain ⟨ζ, hζ⟩ := repK (wq hj hm).2 (wq hj hm).1
    have hW : compA 1755 (fA m) (vA j) = unpack 1755 11 (W m j) := by
      rw [fA_eq (ult m hm), vA_eq (jlt j hj), cmpU (cFL (ult m hm)) cv]
      rfl
    rw [baseTwG_eq bindsK TitsK.head TitsK.hl (NS := 220) (CH := 8) (by norm_num) TitsK.hs ndK htr
      (vq hj).2.2.1 (sKs (vq hj).2.2.1 (vq hj).2.1) (wq hj hm).2 (sKs (wq hj hm).2 (wq hj hm).1),
      hW, vA_eq (jlt j hj), pi_eq, tw2_eq hσ hp1 hν hν' hζ (hrel hj)]
  unfold cTP cTest commInU11
  have e : ([10, 11, 12].all fun i => baseTw TitsK.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (VQ i))
      (pgR (V i))) =
      (commA (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr) (vA 10) &&
        commA (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr) (vA 11) &&
        commA (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr) (vA 12)) := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, tc (i := 10) (by decide),
      tc (i := 11) (by decide), tc (i := 12) (by decide), Bool.and_assoc]
  rw [e]
  congr 1
  exact all_congr_mem fun j hj => any_congr_mem fun m hm => tt hj hm

end KPart

theorem agrK : Agrees TitsK.LR TitsK.TR (fun t0 t1 t2 t3 t4 => !PK' t0 t1 t2 t3 t4)
    (fun a => !pK a) := fun t0 t1 t2 t3 t4 htr => by
  have e : NLoc.PK t0 t1 t2 t3 t4 =
      pK (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) := by
    unfold NLoc.PK pK
    rw [cT_eq htr, cTP_eq htr]
  dsimp only
  unfold NLoc.PK'
  rw [e]
  cases pK (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) <;> rfl

theorem kPart : all5 1755 titsKLevels pK = true :=
  all5_of_nil (surv5K_soundCT (C := []) bindsK permK TitsK.hl agrK (by quickRfl) (by quickRfl) KA.all)

theorem yArr_eq : yArr () = unpack 1755 11 Y ∧ C Y :=
  chain_gen bindsN canN (w := Certificates.TitsAschbacherNLocal.yWord) (by decide)

theorem yi_eq : invCand 1755 (yArr ()) = unpack 1755 11 YI := by
  have k := yK
  simp only [Bool.and_eq_true] at k
  rw [yArr_eq.1]
  exact invCand_unpack k.1

theorem cYI : C YI := by
  have k := yK
  simp only [Bool.and_eq_true] at k
  exact k.2

theorem inv_right {t r : Array Nat} {p : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t p)
    (h : isInvA 1755 t r = true) {i : Nat} (hi : i < 1755) : t[r[i]!]! = i := by
  unfold isInvA at h
  rw [allLt_iff] at h
  have hj := h (p.symm ⟨i, hi⟩).val (p.symm ⟨i, hi⟩).isLt
  have htj : t[(p.symm ⟨i, hi⟩).val]! = i := by
    rw [ht.apply (p.symm ⟨i, hi⟩).isLt]
    simp
  simp only [Bool.and_eq_true, beq_iff_eq] at hj
  rw [htj] at hj
  rw [hj.2, htj]

theorem cancelG {X P Q : Array Nat} {p : Equiv.Perm (Fin 1755)} (hX : X.size = 1755)
    (hP : Rep 1755 P p) (hQ : isInvA 1755 P Q = true) (hQl : ∀ i < 1755, Q[i]! < 1755) :
    compA 1755 (compA 1755 X P) Q = X := by
  apply Array.ext
  · simp only [compA, Array.size_ofFn, hX]
  · intro i h1 h2
    have hi : i < 1755 := by simpa only [compA, Array.size_ofFn] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [getElem!_ofFn_nat _ (hQl i hi), inv_right hP hQ hi, getElem!_pos X i h2]

theorem cancel {X : Array Nat} (hX : X.size = 1755) :
    compA 1755 (compA 1755 X CFSG.Quasithin.titsPiArr) CFSG.Quasithin.piInv = X := by
  obtain ⟨hp1, -⟩ := rep_permOfArr (invEqK_sound (r := PiI) piP).2
  have hinv := (invEqK_sound (r := PiI) piP).2
  obtain ⟨-, -, -, rI⟩ := canonK_facts cPiI
  rw [pi_eq, piInv_eq]
  exact cancelG hX hp1 hinv fun i hi => by rw [unpack_getT hi]; exact rI i hi

theorem unpack_size' (P : Nat) : (unpack 1755 11 P).size = 1755 := by simp [unpack]

theorem inS_false {g : Array Nat} (hz : g[pg 11 (mask 11) TitsS.BP 0]! < 1755)
    (h : out0 (g[pg 11 (mask 11) TitsS.BP 0]!) = true) : inS g = false := by
  have hb0 : (baseArr 1755 titsSBase)[0]! = pg 11 (mask 11) TitsS.BP 0 :=
    bindsS.2.2.2.2.2.2 0 (by norm_num)
  unfold inS
  exact CFSG.KS.Raw.Orb.siftA_false_of_out bindsS permS TitsS.hl (by norm_num) (by rw [hb0]; exact hz)
    (by rw [hb0]; exact h)

section SPart

variable {t0 t1 t2 t3 t4 : Nat} (htr : IsTr5 TitsS.LR TitsS.TR t0 t1 t2 t3 t4)
include htr

theorem gX : ∀ q < 1755, (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))[q]! =
    gptR t0 t1 t2 t3 t4 q ∧ gptR t0 t1 t2 t3 t4 q < 1755 := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := canOf canTRS htr
  obtain ⟨-, hg⟩ := gpt_facts k0 k1 k2 k3 k4
  intro q hq
  rw [gptR_eq]
  exact hg q hq

omit htr in
theorem notInT_of {x : Array Nat} {gx : Nat → Nat} (hx : ∀ q < 1755, x[q]! = gx q ∧ gx q < 1755)
    (h : l0 gx = true) :
    notInT (compA 1755 (compA 1755 (invCand 1755 (yArr ())) x) (yArr ())) = true := by
  obtain ⟨-, -, -, rY⟩ := canonK_facts yArr_eq.2
  obtain ⟨-, -, -, rYI⟩ := canonK_facts cYI
  obtain ⟨-, -, -, rPI⟩ := canonK_facts cPiI
  have hb : pg 11 (mask 11) TitsS.BP 0 < 1755 := by
    rw [← bindsS.2.2.2.2.2.2 0 (by norm_num)]
    exact CFSG.KS.Raw.Orb.base_lt_of_levels bindsS TitsS.hl 0 (by norm_num)
  have ev : ∀ b < 1755, (compA 1755 (compA 1755 (invCand 1755 (yArr ())) x) (yArr ()))[b]! =
      pg 11 (mask 11) YI (gx (pg 11 (mask 11) Y b)) ∧
      pg 11 (mask 11) YI (gx (pg 11 (mask 11) Y b)) < 1755 := by
    intro b hb'
    rw [compA_get hb', yi_eq, yArr_eq.1, unpack_getT hb', compA_get (rY b hb'), (hx _ (rY b hb')).1,
      unpack_getT (hx _ (rY b hb')).2]
    exact ⟨rfl, rYI _ (hx _ (rY b hb')).2⟩
  have hb0 : b0 = pg 11 (mask 11) TitsS.BP 0 := rfl
  unfold l0 at h
  rw [hb0] at h
  simp only [Bool.and_eq_true] at h
  unfold notInT
  rw [inS_false (g := compA 1755 (compA 1755 (invCand 1755 (yArr ())) x) (yArr ()))
    (by rw [(ev _ hb).1]; exact (ev _ hb).2) (by rw [(ev _ hb).1]; exact h.1)]
  have e2 : (compA 1755 (compA 1755 (compA 1755 (invCand 1755 (yArr ())) x) (yArr ()))
      CFSG.Quasithin.piInv)[pg 11 (mask 11) TitsS.BP 0]! =
      pg 11 (mask 11) YI (gx (pg 11 (mask 11) Y (pg 11 (mask 11) PiI
        (pg 11 (mask 11) TitsS.BP 0)))) := by
    rw [compA_get hb, piInv_eq, unpack_getT hb]
    exact (ev _ (rPI _ hb)).1
  rw [inS_false (g := compA 1755 (compA 1755 (compA 1755 (invCand 1755 (yArr ())) x) (yArr ()))
    CFSG.Quasithin.piInv) (by rw [e2]; exact (ev _ (rPI _ hb)).2) (by rw [e2]; exact h.2)]
  rfl

theorem inK_eq : inK (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) =
    ktKB TitsK.LR TitsK.TRI TitsK.BP TitsS.BP t0 t1 t2 t3 t4 := by
  have hKS : ∀ j < 7, siftA 1755 (rawLevels 1755 titsSArrs (baseArr 1755 titsSBase))
      (baseArr 1755 titsSBase) 0 titsKArrs[j]! = true := fun j hj => by
    rw [bindsK.2.2.2.2.1 j hj]
    have c := allN_spec canK j hj
    exact siftK_soundR bindsS permS TitsS.hl rfl (hi_of c) (range_of_canonK c) (allN_spec kInS j hj)
  rw [ktKB_eq bindsK permK TitsK.hl bindsS TitsS.head TitsS.hl (NS := 220) (CH := 8) (by norm_num)
    TitsS.hs ndS hKS htr]
  rfl

theorem pS_of (h : PS t0 t1 t2 t3 t4 = true) :
    pS (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) = true := by
  have hsz := unpack_size' (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)
  unfold PS at h
  unfold pS tTest
  · rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [← inK_eq htr] at h
      simp [h, cancel hsz]
    · simp only [Bool.and_eq_true] at h
      have hx' : ∀ q < 1755, (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          CFSG.Quasithin.titsPiArr)[q]! = gptR t0 t1 t2 t3 t4 (pg 11 (mask 11) Pi q) ∧
          gptR t0 t1 t2 t3 t4 (pg 11 (mask 11) Pi q) < 1755 := by
        obtain ⟨-, -, -, rP⟩ := canonK_facts cPi
        intro q hq
        rw [compA_get hq, pi_eq, unpack_getT hq]
        exact gX htr _ (rP q hq)
      rw [notInT_of (gX htr) h.1, notInT_of hx' h.2]
      rfl

end SPart

theorem agrS : Agrees TitsS.LR TitsS.TR (fun t0 t1 t2 t3 t4 => !PS' t0 t1 t2 t3 t4)
    (fun a => !pS a) := fun t0 t1 t2 t3 t4 htr => by
  dsimp only
  unfold NLoc.PS'
  cases h : NLoc.PS t0 t1 t2 t3 t4
  · rfl
  · rw [pS_of htr h]

theorem sPart : all5 1755 titsSLevels pS = true :=
  all5_of_nil (surv5K_soundCT (C := []) bindsS permS TitsS.hl agrS (by quickRfl) (by quickRfl) SA.all)

theorem kw_lt : ∀ w ∈ kWords, ∀ j ∈ w, j < 13 := by decide

theorem kw_in : ∀ w ∈ kWords, inK (vProd w) = true := by
  have r := e1
  simp only [Bool.and_eq_true] at r
  intro w hw
  obtain ⟨hv, cv⟩ := vProd_eq (kw_lt w hw)
  rw [hv]
  exact sKs cv (List.all_eq_true.1 r.2 w hw)

theorem c1 : inK (compA 1755 CFSG.Quasithin.titsPiArr CFSG.Quasithin.titsPiArr) = true := by
  have r := e1
  simp only [Bool.and_eq_true] at r
  rw [pi_eq, cmpU cPi cPi]
  exact sKs (cmpC cPi cPi) r.1

theorem c2 : kWords.all (fun w => lettersIn 1 12 w && inK (vProd w)) = true := by
  have hl : ∀ w ∈ kWords, lettersIn 1 12 w = true := by decide
  exact List.all_eq_true.2 fun w hw => by rw [hl w hw, kw_in w hw]; rfl

theorem c34 : eqA 1755 (compA 1755 (vProd [4, 5]) (vA 10))
      (compA 1755 (compA 1755 (vA 12) (vA 10)) (vProd [4, 5])) = true ∧
    eqA 1755 (compA 1755 (vProd [1, 5]) (vA 10))
      (compA 1755 (compA 1755 (vA 11) (vA 10)) (vProd [1, 5])) = true := by
  have r := e3
  simp only [Bool.and_eq_true] at r
  obtain ⟨h45, c45⟩ := vProd_eq (l := [4, 5]) (by decide)
  obtain ⟨h15, c15⟩ := vProd_eq (l := [1, 5]) (by decide)
  have c10 := cV (i := 10) (by decide)
  have c11 := cV (i := 11) (by decide)
  have c12 := cV (i := 12) (by decide)
  rw [h45, h15, vA_eq (i := 10) (by decide), vA_eq (i := 11) (by decide), vA_eq (i := 12) (by decide),
    cmpU c45 c10, cmpU c12 c10, cmpU (cmpC c12 c10) c45, eqU (cmpC c45 c10) (cmpC (cmpC c12 c10) c45),
    cmpU c15 c10, cmpU c11 c10, cmpU (cmpC c11 c10) c15, eqU (cmpC c15 c10) (cmpC (cmpC c11 c10) c15)]
  exact ⟨r.1, r.2⟩

theorem c5 : (List.range 32).all (fun m => m % 8 == 0 ||
    kWords.any fun w => !commA (fA m) (vProd w)) = true := by
  refine (all_congr_mem fun m hm => ?_).trans f4
  have hm' : m < 32 := List.mem_range.1 hm
  have cF := cFL hm'
  congr 1
  refine any_congr_mem fun w hw => ?_
  obtain ⟨hv, cv⟩ := vProd_eq (kw_lt w hw)
  rw [fA_eq hm', hv]
  unfold commA
  rw [cmpU cF cv, cmpU cv cF, eqU (cmpC cF cv) (cmpC cv cF)]
  rfl

theorem c6 : (List.range 32).all (fun m => m % 4 == 0 ||
    kWords.any fun w => !commInU11 (fA m) (vProd w)) = true := by
  refine (all_congr_mem fun m hm => ?_).trans f5
  have hm' : m < 32 := List.mem_range.1 hm
  have cF := cFL hm'
  congr 1
  refine any_congr_mem fun w hw => ?_
  obtain ⟨hv, cv⟩ := vProd_eq (kw_lt w hw)
  unfold commInU11
  congr 1
  refine any_congr_mem fun u hu => ?_
  have hu' := ult u hu
  have cU := cFL hu'
  rw [fA_eq hm', fA_eq hu', hv, cmpU cF cv, cmpU cU cv, cmpU (cmpC cU cv) cF,
    eqU (cmpC cF cv) (cmpC (cmpC cU cv) cF)]
  rfl

theorem c14 : (List.range 32).all (fun m => m % 4 == 0 || !commInU10 (yArr ()) (fA m)) = true := by
  refine (all_congr_mem fun m hm => ?_).trans f7
  have hm' : m < 32 := List.mem_range.1 hm
  have cF := cFL hm'
  have cY := yArr_eq.2
  congr 2
  unfold commInU10
  refine any_congr_mem fun i hi => ?_
  have hi' : 4 * i < 32 := by have := List.mem_range.1 hi; omega
  have cU := cFL hi'
  rw [fA_eq hm', fA_eq hi', yArr_eq.1, cmpU cY cF, cmpU cU cF, cmpU (cmpC cU cF) cY,
    eqU (cmpC cY cF) (cmpC (cmpC cU cF) cY)]
  rfl

theorem cy : (nLetters Certificates.TitsAschbacherNLocal.yWord && isInvA 1755 (yArr ()) (invCand 1755 (yArr ())) &&
    eqA 1755 (powA (yArr ()) 3) (idA 1755) && !eqA 1755 (yArr ()) (idA 1755) &&
    commA (yArr ()) (vA 10) && conjEqA (yArr ()) (vA 12) (vA 11) &&
    conjEqA (yArr ()) (compA 1755 (vA 11) (vA 12)) (vA 12)) = true := by
  have r := e6
  simp only [Bool.and_eq_true] at r
  obtain ⟨⟨⟨⟨y3, yne⟩, y10⟩, y12⟩, y1112⟩ := r
  have k := yK
  simp only [Bool.and_eq_true] at k
  have cY := yArr_eq.2
  have c10 := cV (i := 10) (by decide)
  have c11 := cV (i := 11) (by decide)
  have c12 := cV (i := 12) (by decide)
  have hinv : isInvA 1755 (yArr ()) (invCand 1755 (yArr ())) = true := by
    rw [yi_eq, yArr_eq.1]
    exact (invEqK_sound (r := YI) k.1).2
  rw [hinv]
  unfold commA conjEqA
  rw [yArr_eq.1, vA_eq (i := 10) (by decide), vA_eq (i := 11) (by decide), vA_eq (i := 12) (by decide),
    powU cY, TitsCentral.id_eq, eqU (powC cY) TitsCentral.canId, eqU cY TitsCentral.canId,
    cmpU cY c10, cmpU c10 cY,
    eqU (cmpC cY c10) (cmpC c10 cY), cmpU c12 cY, cmpU cY c11, eqU (cmpC c12 cY) (cmpC cY c11),
    cmpU c11 c12, cmpU (cmpC c11 c12) cY, cmpU cY c12, eqU (cmpC (cmpC c11 c12) cY) (cmpC cY c12)]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨by decide, trivial⟩, y3⟩, yne⟩, y10⟩, y12⟩, y1112⟩

theorem kPart' : all5 1755 titsKLevels
    (fun k => cTest k && cTest (compA 1755 k CFSG.Quasithin.titsPiArr)) = true := kPart

theorem sPart' : all5 1755 titsSLevels (fun s => tTest (invCand 1755 (yArr ())) (yArr ()) s &&
    tTest (invCand 1755 (yArr ())) (yArr ()) (compA 1755 s CFSG.Quasithin.titsPiArr)) = true := sPart

theorem nloc_ok : nlocCheck () = true := by
  have hy := cy
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨⟨⟨⟨⟨l1, l2⟩, l3⟩, l4⟩, l5⟩, l6⟩, l7⟩ := hy
  unfold nlocCheck
  simp only [c1, c2, c34.1, c34.2, c5, c6, c14, l1, l2, l3, l4, l5, l6, l7, kPart', sPart',
    Bool.and_true]

end CertificateChecks.Batch27586

namespace Certificates

open CertificateChecks

theorem certificate27586 : Certificates.TitsAschbacherNLocal.nlocCheck () = true := CertificateChecks.Batch27586.nloc_ok

end Certificates
