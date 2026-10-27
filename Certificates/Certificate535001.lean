module

public import Certificates.Data.TitsAschbacherE32NormF
public import Certificates.Kernel.EvenBN.Lists
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch535001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def memK (M : List Nat) (x : Nat) : Bool := strictB x fun y => M.any (Nat.beq y)

@[expose] noncomputable def interK (L M : List Nat) : Nat := (L.filter (memK M)).length

theorem kAll : (xkData.all (fun e => !e.2.1 || (e.2.2 == [] && !e.1) ||
      decide (interK (xkL e) FL ≤ 8)) &&
    !memK EL (V 7) && memK (xkL (xkData.getD 4 (false, false, []))) (V 2) &&
    decide (interK (xkL (xkData.getD 4 (false, false, []))) EL ≤ 8) &&
    (xkL (xkData.getD 4 (false, false, []))).all (fun x => (List.range 5).all fun i =>
      memK EL (pc (pc x (V (8 + i))) x))) = true := by quickRfl

theorem memL_eq {M : List Nat} (hM : ∀ y ∈ M, C y) {x : Nat} (cx : C x) :
    memL (M.map (unpack 1755 11)) (unpack 1755 11 x) = memK M x := by
  unfold memK
  rw [strictB_app]
  exact any_mapU hM fun y cy => eqU cx cy

theorem inter_eq {L M : List Nat} (hL : ∀ y ∈ L, C y) (hM : ∀ y ∈ M, C y) :
    interCount (L.map (unpack 1755 11)) (M.map (unpack 1755 11)) = interK L M := by
  unfold interCount interK
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun x hx => ?_
  simp only [Function.comp]
  exact memL_eq hM (hL x hx)

theorem x4_mem : xkData.getD 4 (false, false, []) ∈ xkData := by decide

theorem tits_e32_norm_check_0 : e32NormCheck () = true := by
  obtain ⟨hX, cX⟩ := xkSet_eq x4_mem
  obtain ⟨h7, c7⟩ := v_eq (i := 7) (by decide)
  obtain ⟨h2, c2⟩ := v_eq (i := 2) (by decide)
  have p1 : xkData.all (fun e => !e.2.1 || (e.2.2 == [] && !e.1) ||
        decide (interCount (xkSet (EL.map (unpack 1755 11)) (FL.map (unpack 1755 11)) e)
          (FL.map (unpack 1755 11)) ≤ 8)) =
      xkData.all (fun e => !e.2.1 || (e.2.2 == [] && !e.1) || decide (interK (xkL e) FL ≤ 8)) := by
    refine all_congr_mem fun e he => ?_
    obtain ⟨hs, cs⟩ := xkSet_eq he
    rw [hs, inter_eq cs fArrs_eq.2]
  have p5 : (List.map (unpack 1755 11) (xkL (xkData.getD 4 (false, false, [])))).all
        (fun x => (List.range 5).all fun i =>
          memL (EL.map (unpack 1755 11)) (compA 1755 (compA 1755 x (vA (8 + i))) x)) =
      (xkL (xkData.getD 4 (false, false, []))).all (fun x => (List.range 5).all fun i =>
        memK EL (pc (pc x (V (8 + i))) x)) := by
    refine all_mapU cX fun x cx => all_congr_mem fun i hi => ?_
    have hi' : 8 + i < 13 := by simp at hi; omega
    obtain ⟨hv, cv⟩ := v_eq hi'
    rw [vA_eq hi', cmpU cx cv, cmpU (cmpC cx cv) cx, memL_eq eArrs_eq.2 (cmpC (cmpC cx cv) cx)]
    rfl
  unfold e32NormCheck
  simp only []
  rw [eArrs_eq.1, fArrs_eq.1, p1, hX, p5, vA_eq (i := 7) (by decide), vA_eq (i := 2) (by decide),
    memL_eq eArrs_eq.2 c7, memL_eq cX c2, inter_eq cX eArrs_eq.2]
  exact kAll

end CertificateChecks.Batch535001

namespace Certificates

open CertificateChecks

theorem certificate535001 : Certificates.TitsAschbacherE32.e32NormCheck () = true := by
  exact CertificateChecks.Batch535001.tits_e32_norm_check_0

end Certificates
