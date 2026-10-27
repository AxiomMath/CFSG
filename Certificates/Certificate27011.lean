module

public import Certificates.Data.TitsAschbacherParrott
public import Certificates.Kernel.EvenBN.Bind
public import CFSG.Certificates.Kernel.Spor.SiftRSound
meta import Certificates.Data.TitsAschbacherParrott
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27011

meta def uList : List (Array Nat) :=
  (List.range 32).map fun a => Certificates.TitsAschbacherParrott.vProd
    (Certificates.TitsAschbacherParrott.u8Bits a)

end CertificateChecks.Batch27011

#kst_plist CertificateChecks.Batch27011.U32 11 CertificateChecks.Batch27011.uList

namespace CertificateChecks.Batch27011

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.SporSch
open CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott

theorem sK : allN 3 (fun j => Nat.beq (TitsS.S j) (wP V (sInV.getD j []))) = true := by quickRfl
theorem wK : allN 3 (fun j => Nat.beq (TitsS.S j) (wP V (sInW.getD j []).flatten)) = true := by
  quickRfl
theorem jK : allN 4 (fun k => Nat.beq (TitsJ.S k) (wP V (jInU.getD k []))) = true := by quickRfl
theorem piK : Nat.beq Pi (wP V piInV) = true := by quickRfl
theorem jS : allN 10 (fun k => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI
    TitsJ.BP 4 0 (pcomp 1755 11 (mask 11) (V (Nat.add k 3))
      (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) PiI
        (parrottWords.getD (Nat.add k 3) ([], false)).2))) = true := by quickRfl
theorem uK : allN 32 (fun a => Nat.beq (wP V (u8Bits a)) (CFSG.KS.Mathieu.nget U32 a)) = true := by
  quickRfl
theorem uD : pairNe U32 = true := by quickRfl
theorem uLB : Nat.beq U32.length 32 = true := by quickRfl
theorem uL : U32.length = 32 := Nat.eq_of_beq_eq_true uLB

theorem negPi : (Nat.beq Pi (wP V [4, 5, 5])).not = true := by quickRfl

theorem negD : (pairNe (U32.head! :: U32)).not = true := by quickRfl

theorem canJ' : allN 9 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsJ.S j)) = true := canJ

theorem gen_eqA {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP k : Nat} {base : Array Nat}
    (hb : Binds 1755 11 PS kS nb BP A base)
    (hc : allN kS (fun j => canonK 1755 11 (mask 11) (1755 * 11) (PS j)) = true)
    {L : Nat → List Nat} (hk : k ≤ kS) (hL : ∀ j < k, ∀ i ∈ L j, i < 13)
    (h : allN k (fun j => Nat.beq (PS j) (wP V (L j))) = true) :
    (List.range k).all (fun j => eqA 1755 A[j]! (vProd (L j))) = true := by
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := List.mem_range.1 hj
  obtain ⟨e, c⟩ := vProd_eq (hL j hj')
  rw [hb.2.2.2.2.1 j (by omega), e, eqU (allN_spec hc j (by omega)) c]
  exact allN_spec h j hj'

theorem optI_eq (o : Bool) : (if o = true then piInv else idA 1755) =
    unpack 1755 11 (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) PiI o) ∧
    C (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) PiI o) := by
  cases o
  · exact ⟨CertificateChecks.KernelSporSch.TitsCentral.id_eq, canId⟩
  · exact ⟨piInv_eq, cPiI⟩

theorem jPart : (List.range' 3 10).all (fun i =>
    inJ (compA 1755 (vA i) (if (parrottWords.getD i ([], false)).2 then piInv else idA 1755))) =
      true := by
  refine List.all_eq_true.2 fun i hi => ?_
  obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  obtain ⟨e, c⟩ := optI_eq (parrottWords.getD (k + 3) ([], false)).2
  have cv := cV (i := k + 3) (by omega)
  rw [vA_eq (by omega), e, cmpU cv c]
  have cg := cmpC cv c
  exact siftK_soundR bindsJ permJ TitsJ.hl rfl (hi_of cg) (range_of_canonK cg)
    (allN_spec jS k (by omega))

theorem u8_lt (a : Nat) : ∀ j ∈ u8Bits a, j < 13 := by
  intro j hj
  simp only [u8Bits, List.mem_filterMap, List.mem_range] at hj
  obtain ⟨k, hk, h⟩ := hj
  split at h
  · cases h
    omega
  · cases h

theorem uC {a : Nat} (ha : a < 32) : vProd (u8Bits a) = unpack 1755 11 (CFSG.KS.Mathieu.nget U32 a) ∧
    C (CFSG.KS.Mathieu.nget U32 a) := by
  rw [← Nat.eq_of_beq_eq_true (allN_spec uK a ha)]
  exact vProd_eq (u8_lt a)

theorem u_ne {a b : Nat} (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    Nat.beq (CFSG.KS.Mathieu.nget U32 a) (CFSG.KS.Mathieu.nget U32 b) = false := by
  have hp : ∀ (i j : Nat) (hi : i < U32.length) (hj : j < U32.length), i < j →
      Nat.beq U32[i] U32[j] = false := List.pairwise_iff_getElem.1 (pairNe_spec uD)
  rw [nget_get U32 (by rw [uL]; exact ha), nget_get U32 (by rw [uL]; exact hb)]
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact hp a b (by rw [uL]; exact ha) (by rw [uL]; exact hb) h
  · have := hp b a (by rw [uL]; exact hb) (by rw [uL]; exact ha) h
    cases e : Nat.beq U32[a] U32[b]
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e).symm (Nat.ne_of_beq_eq_false this)

theorem dPart : ((List.range 32).all fun a => (List.range 32).all fun b =>
    a == b || !eqA 1755 (vProd (u8Bits a)) (vProd (u8Bits b))) = true := by
  refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb => ?_
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  by_cases hab : a = b
  · subst hab
    simp
  · obtain ⟨ea, ca⟩ := uC ha'
    obtain ⟨eb, cb⟩ := uC hb'
    rw [ea, eb, eqU ca cb, u_ne ha' hb' hab]
    simp

theorem tits_parrott_check_0 : genCheck = true := by
  have e3 : ∀ j < 3, ∀ i ∈ sInV.getD j [], i < 13 := by decide
  have f3 : ∀ j < 3, ∀ i ∈ (sInW.getD j []).flatten, i < 13 := by decide
  have g4 : ∀ j < 4, ∀ i ∈ jInU.getD j [], i < 13 := by decide
  obtain ⟨ep, cp⟩ := vProd_eq (l := piInV) (by decide)
  have pS : eqA 1755 titsPiArr (vProd piInV) = true := by
    rw [pi_eq, ep, eqU cPi cp]
    exact piK
  unfold genCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gen_eqA bindsS canS (by norm_num) e3 sK, pS⟩, by decide⟩, by decide⟩,
    gen_eqA bindsS canS (by norm_num) f3 wK⟩, by decide⟩, jPart⟩,
    gen_eqA bindsJ canJ' (by norm_num) g4 jK⟩, pS⟩, by decide⟩, by decide⟩, dPart⟩

end CertificateChecks.Batch27011

namespace Certificates

open CertificateChecks

theorem certificate27011 : Certificates.TitsAschbacherParrott.genCheck = true := by
  exact CertificateChecks.Batch27011.tits_parrott_check_0

end Certificates
