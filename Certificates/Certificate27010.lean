module

public import Certificates.Data.TitsAschbacherParrott
public import Certificates.Kernel.EvenBN.Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27010

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelSporSch.TitsCommon CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott

theorem sqK : allN 12 (fun t => Nat.beq (pcomp 1755 11 (mask 11) (V (t + 1)) (V (t + 1)))
    (wP V (parrottSq (t + 1)))) = true := by quickRfl

theorem neK : allN 12 (fun t => !Nat.beq (V (t + 1)) (pidn 1755 11)) = true := by quickRfl

theorem commK : parrottComm.all (fun r => Nat.beq (pcomp 1755 11 (mask 11) (V r.1) (V r.2.1))
    (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (V r.2.1) (V r.1)) (wP V r.2.2))) = true := by
  quickRfl

theorem cmK : allN 12 (fun a => allN 12 (fun b => listed (a + 1) (b + 1) || listed (b + 1) (a + 1) ||
    Nat.beq (pcomp 1755 11 (mask 11) (V (a + 1)) (V (b + 1)))
      (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (V (b + 1)) (V (a + 1))) (pidn 1755 11))))
    = true := by quickRfl

theorem zK : Nat.beq (V 12) KernelSporSch.TitsZ = true := by quickRfl

theorem sqLet : ∀ i < 13, ∀ x ∈ parrottSq i, x < 13 := by decide

theorem commLet : ∀ r ∈ parrottComm, r.1 < 13 ∧ r.2.1 < 13 ∧ ∀ x ∈ r.2.2, x < 13 := by decide

theorem idx {i : Nat} (hi : i ∈ List.range' 1 12) : ∃ t, i = t + 1 ∧ t < 12 := by
  obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hi
  exact ⟨i - 1, by omega, by omega⟩

theorem sqPart : sqOK = true := by
  unfold sqOK
  refine List.all_eq_true.2 fun i hi => ?_
  obtain ⟨t, rfl, ht⟩ := idx hi
  have c := cV (i := t + 1) (by omega)
  obtain ⟨e, ce⟩ := vProd_eq (sqLet (t + 1) (by omega))
  rw [vA_eq (by omega), cmpU c c, e, eqU (cmpC c c) ce]
  exact allN_spec sqK t ht

theorem nePart : neOneOK = true := by
  unfold neOneOK
  refine List.all_eq_true.2 fun i hi => ?_
  obtain ⟨t, rfl, ht⟩ := idx hi
  rw [vA_eq (by omega), CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (cV (by omega)) canId]
  exact allN_spec neK t ht

theorem commPart : Certificates.TitsAschbacherParrott.commOK = true := by
  unfold Certificates.TitsAschbacherParrott.commOK
  refine List.all_eq_true.2 fun r hr => ?_
  obtain ⟨l1, l2, l3⟩ := commLet r hr
  have c1 := cV l1
  have c2 := cV l2
  obtain ⟨e, ce⟩ := vProd_eq l3
  unfold commEqA
  rw [vA_eq l1, vA_eq l2, e, cmpU c1 c2, cmpU c2 c1, cmpU (cmpC c2 c1) ce,
    eqU (cmpC c1 c2) (cmpC (cmpC c2 c1) ce)]
  exact List.all_eq_true.1 commK r hr

set_option simprocs false in
theorem cmPart : commuteOK = true := by
  unfold commuteOK
  refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_
  obtain ⟨a, rfl, ha⟩ := idx hi
  obtain ⟨b, rfl, hb⟩ := idx hj
  have ca := cV (i := a + 1) (by omega)
  have cb := cV (i := b + 1) (by omega)
  unfold commEqA
  simp only [vA_eq (i := a + 1) (by omega), vA_eq (i := b + 1) (by omega),
    CertificateChecks.KernelSporSch.TitsCentral.id_eq, cmpU ca cb, cmpU cb ca,
    cmpU (cmpC cb ca) canId, eqU (cmpC ca cb) (cmpC (cmpC cb ca) canId)]
  exact allN_spec (allN_spec cmK a ha) b hb

theorem zPart : eqA 1755 (vA 12) titsZArr = true := by
  rw [vA_eq (by omega), z_eq, eqU (cV (by omega)) canonZ]
  exact zK

theorem tits_parrott_check_0 : relCheck = true := by
  unfold relCheck
  rw [sqPart, nePart, commPart, cmPart, zPart]
  rfl

end CertificateChecks.Batch27010

namespace Certificates

open CertificateChecks

theorem certificate27010 : Certificates.TitsAschbacherParrott.relCheck = true := by
  exact CertificateChecks.Batch27010.tits_parrott_check_0

end Certificates
