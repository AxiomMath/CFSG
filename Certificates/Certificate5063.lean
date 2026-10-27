module

public import CFSG.GH74.GLS.C3.Layer2.L5C4bInputs
import CFSG.Certificates.Kernel.L5.Fast
import Std.Tactic.BVDecide.Normalize.BitVec

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5063

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem sh0_trMem_chk_0 : (List.finRange 16).all (fun v => decide (tr16 v ∈ Sh0L)) = true := by
  decide +kernel

private theorem sh0_secMem_chk_1 : (List.finRange 8).all (fun k => decide (Dg k ∈ Sh0L)) = true := by
  decide +kernel

private theorem tr16_xor_chk_2 : (List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr16 (xor16 u v) = tr16 u * tr16 v)) = true := by
  decide +kernel

private theorem tr16_zero_3 : tr16 0 = 1 := by
  decide +kernel

private theorem sh0_dec_chk_4 : Sh0L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
    decide (p = tr16 v * Dg k)) = true := by
  decide +kernel

private def pc (p : Perm (Fin 16)) : ℕ := (List.finRange 16).foldl (fun acc i => acc * 16 + (p i).val) 0

private def pairs16x8 : List (Fin 16 × Fin 8) :=
  (List.finRange 16).flatMap fun v => (List.finRange 8).map fun k => (v, k)

private theorem uniq_of_codes {A : Fin 16 → Fin 8 → Perm (Fin 16)}
    (h : (pairs16x8.map fun x => pc (A x.1 x.2)).Nodup) :
    (List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
      (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
        imp (decide (A v k = A v' k')) (decide (v = v' ∧ k = k'))) = true := by
  simp only [List.all_eq_true]
  intro v _ k _ v' _ k' _
  by_cases e : A v k = A v' k'
  · have hm : ∀ a b, (a, b) ∈ pairs16x8 := fun a b => by simp [pairs16x8]
    have hx := List.inj_on_of_nodup_map h (hm v k) (hm v' k') (by simp only [e])
    simp only [Prod.mk.injEq] at hx
    simp [imp, hx]
  · simp [imp, e]

private theorem sh0_uniq_chk_5 : (List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr16 v * Dg k = tr16 v' * Dg k')) (decide (v = v' ∧ k = k'))) = true :=
  uniq_of_codes (A := fun v k => tr16 v * Dg k) (by decide +kernel)

private theorem sh1_L_chk_6 : ((List.finRange 16).all (fun v => decide (tr1 v ∈ Sh1L)) &&
    (List.finRange 8).all (fun k => decide (tau1 k ∈ Sh1L)) &&
    Sh1L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
      decide (p = tr1 v * tau1 k))) = true := by
  have e1 : ∀ v, tr1 v = ((tr1L.map PkCV.cOf).map PkCV.ev).getD v.val 1 := fun v => by
    rw [PkCV.map_cOf_ev]
    rfl
  have e2 : ∀ k, tau1 k = ((tau1L.map PkCV.cOf).map PkCV.ev).getD k.val 1 := fun k => by
    rw [PkCV.map_cOf_ev]
    rfl
  have e3 : Sh1L = (closureList (sh1Gens.map PkCV.cOf) 12).map PkCV.ev := by
    rw [← PkCV.closureList_map_ev, PkCV.map_cOf_ev]
    rfl
  simp only [e1, e2, e3]
  decide +kernel

private theorem tr1_xor_chk_7 : (List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr1 (xor16 u v) = tr1 u * tr1 v)) = true := by
  decide +kernel

private theorem tau1_zero_8 : tau1 0 = 1 := by
  decide +kernel

private theorem sh1_conj_chk_9 : (List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (tau1 j * tr1 w = tr1 (Dg j w) * tau1 j)) = true := by
  decide +kernel

private theorem sh1_mul_chk_10 : (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (tau1 j * tau1 k = tr1 (cc1 j k) * tau1 (mulIdx j k))) = true := by
  decide +kernel

private theorem sh1_uniq_chk_11 : (List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr1 v * tau1 k = tr1 v' * tau1 k')) (decide (v = v' ∧ k = k'))) = true :=
  uniq_of_codes (A := fun v k => tr1 v * tau1 k) (by decide +kernel)

private theorem sh1_yHat1_chk_12 : (List.finRange 16).any (fun v => decide (yHat1 = tr1 v * tau1 1)) = true := by
  decide +kernel

private theorem yHat1_sq_13 : yHat1 * yHat1 = 1 := by
  decide +kernel

private theorem yHat_sq_14 : yHat * yHat = 1 := by
  decide +kernel

end CertificateChecks.Batch5063

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5063 : ((List.finRange 16).all (fun v => decide (tr16 v ∈ Sh0L)) = true)
    ∧ ((List.finRange 8).all (fun k => decide (Dg k ∈ Sh0L)) = true)
    ∧ ((List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr16 (xor16 u v) = tr16 u * tr16 v)) = true)
    ∧ (tr16 0 = 1)
    ∧ (Sh0L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
    decide (p = tr16 v * Dg k)) = true)
    ∧ ((List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr16 v * Dg k = tr16 v' * Dg k')) (decide (v = v' ∧ k = k'))) = true)
    ∧ (((List.finRange 16).all (fun v => decide (tr1 v ∈ Sh1L)) &&
    (List.finRange 8).all (fun k => decide (tau1 k ∈ Sh1L)) &&
    Sh1L.all (fun p => (List.finRange 16).any fun v => (List.finRange 8).any fun k =>
      decide (p = tr1 v * tau1 k))) = true)
    ∧ ((List.finRange 16).all (fun u => (List.finRange 16).all fun v =>
    decide (tr1 (xor16 u v) = tr1 u * tr1 v)) = true)
    ∧ (tau1 0 = 1)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (tau1 j * tr1 w = tr1 (Dg j w) * tau1 j)) = true)
    ∧ ((List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (tau1 j * tau1 k = tr1 (cc1 j k) * tau1 (mulIdx j k))) = true)
    ∧ ((List.finRange 16).all (fun v => (List.finRange 8).all fun k =>
    (List.finRange 16).all fun v' => (List.finRange 8).all fun k' =>
      imp (decide (tr1 v * tau1 k = tr1 v' * tau1 k')) (decide (v = v' ∧ k = k'))) = true)
    ∧ ((List.finRange 16).any (fun v => decide (yHat1 = tr1 v * tau1 1)) = true)
    ∧ (yHat1 * yHat1 = 1)
    ∧ (yHat * yHat = 1) := by
  exact ⟨CertificateChecks.Batch5063.sh0_trMem_chk_0, CertificateChecks.Batch5063.sh0_secMem_chk_1, CertificateChecks.Batch5063.tr16_xor_chk_2, CertificateChecks.Batch5063.tr16_zero_3, CertificateChecks.Batch5063.sh0_dec_chk_4, CertificateChecks.Batch5063.sh0_uniq_chk_5, CertificateChecks.Batch5063.sh1_L_chk_6, CertificateChecks.Batch5063.tr1_xor_chk_7, CertificateChecks.Batch5063.tau1_zero_8, CertificateChecks.Batch5063.sh1_conj_chk_9, CertificateChecks.Batch5063.sh1_mul_chk_10, CertificateChecks.Batch5063.sh1_uniq_chk_11, CertificateChecks.Batch5063.sh1_yHat1_chk_12, CertificateChecks.Batch5063.yHat1_sq_13, CertificateChecks.Batch5063.yHat_sq_14⟩

end Certificates
