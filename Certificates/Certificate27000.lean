module

public import Certificates.Data.TitsAschbacherStar
public import Certificates.Kernel.EvenBN.CNtEq
public import Certificates.Kernel.EvenBN.Lists
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherStar

@[expose] noncomputable def sqKf (T : Nat) (u : Nat → Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (u (u i)) (pg 11 (mask 11) T i))

@[expose] noncomputable def commKf (W : Nat) (u : Nat → Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (pg 11 (mask 11) W (u i)) (u (pg 11 (mask 11) W i)))

@[expose] noncomputable def uwuKf (W : Nat) (u : Nat → Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (u (pg 11 (mask 11) W (u i))) (pg 11 (mask 11) W i))

@[expose] noncomputable def starKf (W T : Nat) (u : Nat → Nat) : Bool :=
  !sqKf T u || (!commKf W u && !uwuKf W u)

@[expose] noncomputable def Wt : Nat := PN (CNtC.getD 8 0)

@[expose] noncomputable def starK2 (W A c : Nat) : Bool :=
  starKf W TitsT (pg 11 (mask 11) c) &&
    starKf W TitsT (fun i => pg 11 (mask 11) A (pg 11 (mask 11) c i))

@[expose] noncomputable def starKs (L : List Nat) : Bool :=
  strictB Wt (fun W => strictB (TAux.F 0) (fun A => L.all fun k => strictB (PN k) (starK2 W A)))

theorem s0 : starKs (CNtC.take 128) = true := by quickRfl
theorem s1 : starKs ((CNtC.drop 128).take 128) = true := by quickRfl
theorem s2 : starKs ((CNtC.drop 256).take 128) = true := by quickRfl
theorem s3 : starKs ((CNtC.drop 384).take 128) = true := by quickRfl
theorem s4 : starKs ((CNtC.drop 512).take 128) = true := by quickRfl
theorem s5 : starKs ((CNtC.drop 640).take 128) = true := by quickRfl
theorem s6 : starKs ((CNtC.drop 768).take 128) = true := by quickRfl
theorem s7 : starKs ((CNtC.drop 896).take 128) = true := by quickRfl
theorem s8 : starKs ((CNtC.drop 1024).take 128) = true := by quickRfl
theorem s9 : starKs ((CNtC.drop 1152).take 128) = true := by quickRfl
theorem s10 : starKs ((CNtC.drop 1280).take 128) = true := by quickRfl
theorem s11 : starKs (CNtC.drop 1408) = true := by quickRfl

theorem all_of_chunks {f : Nat → Bool} {L : List Nat} : ∀ (k m : Nat), L.length ≤ m + 128 * k →
    (∀ i < k, ((L.drop (m + 128 * i)).take 128).all f = true) → (L.drop m).all f = true
  | 0, m, hl, _ => by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | k + 1, m, hl, h => by
    rw [← List.take_append_drop 128 (L.drop m), List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    rw [List.drop_drop]
    refine all_of_chunks k (m + 128) (by omega) fun i hi => ?_
    have e : m + 128 + 128 * i = m + 128 * (i + 1) := by ring
    rw [e]
    exact h (i + 1) (by omega)

theorem starKs_eq (L : List Nat) : starKs L = L.all fun k => starK2 Wt (TAux.F 0) (PN k) := by
  unfold starKs
  simp only [KernelEvenBN.strictB_app]

theorem starK_all : (CNtC.all fun k => starK2 Wt (TAux.F 0) (PN k)) = true := by
  have h := all_of_chunks (f := fun k => starK2 Wt (TAux.F 0) (PN k)) (L := CNtC) 12 0
    (by rw [cnt_len]) fun i hi => by
    rw [← starKs_eq]
    interval_cases i
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9
    · exact s10
    · rw [List.take_of_length_le (by simp [cnt_len])]
      exact s11
  simpa using h

theorem sqKf_eq {T : Nat} {u : Nat → Nat} {a : Array Nat} (ha : ∀ i < 1755, a[i]! = u i)
    (hr : ∀ i < 1755, u i < 1755) :
    sqKf T u = eqA 1755 (compA 1755 a a) (unpack 1755 11 T) := by
  unfold sqKf
  refine allN_eq_eqA fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, ha i hi, ha _ (hr i hi), unpack_getT hi, Nat.beq_eq]

theorem commKf_eq {W : Nat} (cW : C W) {u : Nat → Nat} {a : Array Nat}
    (ha : ∀ i < 1755, a[i]! = u i) (hr : ∀ i < 1755, u i < 1755) :
    commKf W u = eqA 1755 (compA 1755 (unpack 1755 11 W) a) (compA 1755 a (unpack 1755 11 W)) := by
  obtain ⟨-, -, -, rW⟩ := canonK_facts cW
  unfold commKf
  refine allN_eq_eqA fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hi, ha i hi,
    unpack_getT (hr i hi), unpack_getT hi, ha _ (rW i hi), Nat.beq_eq]

theorem uwuKf_eq {W : Nat} (cW : C W) {u : Nat → Nat} {a : Array Nat}
    (ha : ∀ i < 1755, a[i]! = u i) (hr : ∀ i < 1755, u i < 1755) :
    uwuKf W u = eqA 1755 (compA 1755 (compA 1755 a (unpack 1755 11 W)) a)
      (unpack 1755 11 W) := by
  obtain ⟨-, -, -, rW⟩ := canonK_facts cW
  unfold uwuKf
  refine allN_eq_eqA fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, ha i hi, CFSG.Monster.B.Co2.compA_get (hr i hi),
    unpack_getT (hr i hi), ha _ (rW _ (hr i hi)), unpack_getT hi, Nat.beq_eq]

theorem starKf_eq {W : Nat} (cW : C W) (hw : starWit = unpack 1755 11 W) {u : Nat → Nat}
    {a : Array Nat} (ha : ∀ i < 1755, a[i]! = u i) (hr : ∀ i < 1755, u i < 1755) :
    starOK a = starKf W TitsT u := by
  unfold starOK escapes starKf commA
  rw [hw, t_eq, ← sqKf_eq ha hr, ← commKf_eq cW ha hr, ← uwuKf_eq cW ha hr]

theorem tits_star_check_0 : starCheck = true := by
  have cW : C Wt := cnt_canon _ (cnt_mem (by decide))
  have hw : starWit = unpack 1755 11 Wt := cnt_getD (by decide) _
  obtain ⟨-, -, -, rA⟩ := canonK_facts cAux
  have h := starK_all
  unfold starCheck
  rw [cnt_eq, List.all_map, aux_eq, ← h]
  refine all_congr_mem fun k hk => ?_
  obtain ⟨-, -, -, rc⟩ := canonK_facts (cnt_canon k hk)
  simp only [Function.comp_apply]
  unfold starK2
  rw [starKf_eq cW hw (fun i hi => unpack_getT hi) rc,
    starKf_eq cW hw (u := fun i => pg 11 (mask 11) (TAux.F 0) (pg 11 (mask 11) (PN k) i))
      (fun i hi => by rw [CFSG.Monster.B.Co2.compA_get hi, unpack_getT hi, unpack_getT (rc i hi)])
      (fun i hi => rA _ (rc i hi))]

end CertificateChecks.Batch27000

namespace Certificates

open CertificateChecks

theorem certificate27000 : Certificates.TitsAschbacherStar.starCheck = true := by
  exact CertificateChecks.Batch27000.tits_star_check_0

end Certificates
