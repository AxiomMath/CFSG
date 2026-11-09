module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.Fi24.Data
import CFSG.Certificates.Kernel.Spor.F3LaneEq
import CFSG.Certificates.Kernel.Spor.F3LaneSound
import CFSG.Certificates.Kernel.Spor.Mat3Sound
import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Br.Rels
import Certificates.Kernel.SporDet.Fi24
import CFSG.Sporadic.Fi24.SetupBase
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi24

namespace CertificateChecks.Batch9001

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi24

private theorem idM_eq : idM 781 = unlane 781 LI := idM_of_idOK id_ok

private theorem ent_bits {n : Nat} {a b : Bool} (hab : (a && b) = false)
    (h : (n : ZMod 3) = CFSG.KS.Mat3.bv a b) :
    decide (n % 3 = 1) = a ∧ decide (n % 3 = 2) = b := by
  rw [← ZMod.natCast_mod] at h
  have ht : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = t at h ht ⊢
  cases a <;> cases b <;> interval_cases t <;> simp_all [CFSG.KS.Mat3.bv] <;> exact absurd h (by decide)

private theorem rowsOf_of_decode {d N X : Nat} {s : String} {L : V}
    (hdec : CFSG.Blueprint.NativeSporadic.decode 3 d 1 s = CFSG.KS.Mat3.mat3 d N X)
    (hN : d * d ≤ N)
    {M : Nat} (hM : M = Nat.sub (Nat.shiftLeft 1 N) 1)
    (hp : Nat.beq L.p (Nat.land X M) = true)
    (hm : Nat.beq L.m (Nat.shiftRight X N) = true) (hw : L.wf = true) :
    rowsOf d s = unlane d L := by
  have hp' : L.p = X % 2 ^ N := by
    rw [Nat.eq_of_beq_eq_true hp, hM, CFSG.KS.Mat3.pow_sub_one_eq]
    exact Nat.and_two_pow_sub_one_eq_mod X N
  have hm' : L.m = X >>> N := Nat.eq_of_beq_eq_true hm
  have hent : ∀ i j (hi : i < d) (hj : j < d),
      (((decodeEntries s)[i * d + j]?.getD 0 : ℕ) : ZMod 3) =
        CFSG.KS.Mat3.bv (L.p.testBit (d * i + j)) (L.m.testBit (d * i + j)) := by
    intro i j hi hj
    have hk : d * i + j < N := by
      have : d * i + j < d * (i + 1) := by rw [Nat.mul_succ]; omega
      exact lt_of_lt_of_le this (le_trans (Nat.mul_le_mul_left _ (by omega)) hN)
    have h := congrFun (congrFun hdec ⟨i, hi⟩) ⟨j, hj⟩
    simp only [CFSG.Blueprint.NativeSporadic.decode, CFSG.KS.Mat3.mat3, ite_true] at h
    rw [hp', hm', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [hk, decide_true, Bool.true_and]
    exact h
  apply Array.ext
  · unfold rowsOf
    rw [Array.size_ofFn, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    have hr : (rowsOf d s)[i]! =
        V.ofFn d (fun j => (decodeEntries s).toArray[i * d + j]?.getD 0) := by
      unfold rowsOf
      rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
    rw [← getElem!_pos (unlane d L) i h2, unlane_get L hi, ← getElem!_pos (rowsOf d s) i h1, hr,
      ofFn_eq_fold]
    apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro j
    · rw [(fold_ofFnStep_bits _ j d).1, blk_p]
      by_cases hj : j < d
      · simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray]
        exact (ent_bits (V.not_both hw _) (hent i j hi hj)).1
      · simp [hj]
    · rw [(fold_ofFnStep_bits _ j d).2, blk_m]
      by_cases hj : j < d
      · simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray]
        exact (ent_bits (V.not_both hw _) (hent i j hi hj)).2
      · simp [hj]

private theorem rowsA : rowsOf 781 Native.seedA = unlane 781 LA := by
  have h : CFSG.Blueprint.NativeSporadic.decode 3 781 1 Native.seedA =
      CFSG.KS.Mat3.mat3 781 609961 (CFSG.KD.BrFi24.RB 23) := by
    rw [CFSG.Sporadic.Fi24.seedA_eq]
    exact CertificateChecks.KernelSpor.Fi24Rels.mA_eq
  exact rowsOf_of_decode (N := 609961) (X := CFSG.KD.BrFi24.RB 23) (M := CFSG.KD.BrFi24.LO) h
    (by norm_num) rfl laneAp_ok laneAm_ok laneAw_ok

private theorem rowsB : rowsOf 781 Native.seedB = unlane 781 LB := by
  have h : CFSG.Blueprint.NativeSporadic.decode 3 781 1 Native.seedB =
      CFSG.KS.Mat3.mat3 781 609961 (CFSG.KD.BrFi24.RB 24) := by
    rw [CFSG.Sporadic.Fi24.seedB_eq]
    exact CertificateChecks.KernelSpor.Fi24Rels.mB_eq
  exact rowsOf_of_decode (N := 609961) (X := CFSG.KD.BrFi24.RB 24) (M := CFSG.KD.BrFi24.LO) h
    (by norm_num) rfl laneBp_ok laneBm_ok laneBw_ok

private theorem rows_B_cube :
    eqM 781 (powM 781 (rowsOf 781 Native.seedB) 3) (idM 781) = true := by
  have hd : 0 < 781 := by norm_num
  simp only [rowsB, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq b3_ok

private theorem rows_AB_pow :
    eqM 781 (powM 781 (mul 781 (rowsOf 781 Native.seedA) (rowsOf 781 Native.seedB)) 29)
      (idM 781) = true := by
  have hd : 0 < 781 := by norm_num
  simp only [rowsA, rowsB, mul_unlane hd, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq ab29_ok

end CertificateChecks.Batch9001

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24 in
open CFSG.F3.Native in
theorem certificate9001 : (eqM 781 (powM 781 (CFSG.F3.Native.rowsOf 781 Native.seedB) 3) (CFSG.F3.Native.idM 781) = true)
    ∧ (eqM 781 (powM 781 (CFSG.F3.Native.mul 781 (CFSG.F3.Native.rowsOf 781 Native.seedA) (CFSG.F3.Native.rowsOf 781 Native.seedB)) 29)
      (CFSG.F3.Native.idM 781) = true) :=
  ⟨CertificateChecks.Batch9001.rows_B_cube, CertificateChecks.Batch9001.rows_AB_pow⟩

end Certificates

end
