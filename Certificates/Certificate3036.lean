module

public import Certificates.Kernel.MonsterB.IndCentral
public import Certificates.Kernel.MonsterB.IndOrbGlue

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.IndOrb CFSG.KC.U6Orb
  CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbGlue
  CertificateChecks.KernelMonB.IndCentral
open CertificateChecks.KernelMonB.IndOrbChecks (kWInv kZInv)

namespace CertificateChecks.Batch3036

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.IndOrb CFSG.KC.U6Orb
  CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbGlue
  CertificateChecks.KernelMonB.IndCentral
open CertificateChecks.KernelMonB.IndOrbChecks (kWInv kZInv)

theorem central_get {y : ℕ} (hy : y < 3510) : indCentral[y]! = fget (ICe.F 0) y 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ICe.all 0 (by norm_num)
  rw [← ICe.eq, Nat.mul_zero] at h
  change (hexTable3 3510 0 indCentralHex)[y]! = _
  rw [h, CFSG.KS.Raw.Orb.unpack_get hy, pg_eq]

theorem map_of {o n b : ℕ} {P : ℕ} {f : ℕ → ℕ} (hP : ∀ j < n, fget P (o + j) 12 < 2464)
    (h : mapOK (ICe.F 0) P 12 o n b f = true) (hb : b + 2464 ≤ 3510) :
    ∀ u ∈ orbL P 12 o n, indCentral[b + u]! = f u := by
  intro u hu
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hu
  rw [central_get (by have := hP j hj; omega)]
  exact mapOK_sound h j hj

theorem wpt {o n j : ℕ} (hon : o + n ≤ 1024) (hj : j < n) : fget (IW 0) (o + j) 12 < 2464 := by
  have := (invTabOK_sound kWInv (o + j) (by omega)).1
  omega

theorem zpt {o n j : ℕ} (hon : o + n ≤ 2464) (hj : j < n) : fget (IZ 0) (o + j) 12 < 2464 :=
  (invTabOK_sound kZInv (o + j) (by omega)).1

theorem central_check_0 :
    (∀ n < 22, 22 ≤ indCentral[n]! ∧ indCentral[n]! < 1046 ∧
      red 12 pivK rowK (spreadW (indCentral[n]! - 22) ^^^ 2 ^ n) = 0) ∧
    (∀ u ∈ (wCert 1).pts.toList, indCentral[22 + u]! < 22 ∧
      red 12 pivK rowK (spreadW u ^^^ 2 ^ indCentral[22 + u]!) = 0) ∧
    (∀ u ∈ (wCert 0).pts.toList, indCentral[22 + u]! = 22 + u) ∧
    (∀ u ∈ (wCert 3).pts.toList, indCentral[22 + u]! = 22 + u) ∧
    (∀ u ∈ (wCert 7).pts.toList, indCentral[22 + u]! = 1046 + sigmaFun u) ∧
    (∀ n ∈ (zCert 0).pts.toList, indCentral[1046 + n]! = 1046 + n) ∧
    (∀ n ∈ (zCert 24).pts.toList, 22 ≤ indCentral[1046 + n]! ∧
      indCentral[1046 + n]! - 22 ∈ (wCert 7).pts.toList ∧
      sigmaFun (indCentral[1046 + n]! - 22) = n) ∧
    (∀ n ∈ (zCert 1).pts.toList, indCentral[1046 + n]! = 1046 + tauFun n) := by
  rw [w0, w1, w3, w7, z0, z24, z1]
  refine ⟨fun n hn => ?_, fun u hu => ?_, map_of (fun j hj => wpt (by norm_num) hj)
    kW0 (by norm_num), map_of (fun j hj => wpt (by norm_num) hj) kW3 (by norm_num),
    fun u hu => ?_, map_of (fun j hj => zpt (by norm_num) hj) kZ0 (by norm_num),
    fun n hn => ?_, fun n hn => ?_⟩
  · rw [central_get (by omega)]
    exact kX n hn
  · obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hu
    rw [central_get (by have := wpt (o := 1) (n := 22) (by norm_num) hj; omega)]
    exact kW1 j hj
  · rw [map_of (fun j hj => wpt (by norm_num) hj) kW7 (by norm_num) u hu,
      sigma_tab hu]
    rfl
  · obtain ⟨j, hj, rfl⟩ := mem_orbL.1 hn
    obtain ⟨h1, h2, h3⟩ := backOK_sound kZ24 j hj
    rw [central_get (by have := zpt (o := 462) (n := 770) (by norm_num) hj; omega)]
    have hm := mem_w7.2 h2
    exact ⟨h1, hm, by rw [sigma_tab hm, h3]⟩
  · rw [map_of (fun j hj => zpt (by norm_num) hj) kZ1 (by norm_num) n hn,
      tau_tab hn]
    rfl

end CertificateChecks.Batch3036

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer in
theorem certificate3036 : (∀ n < 22, 22 ≤ indCentral[n]! ∧ indCentral[n]! < 1046 ∧
        red 12 pivK rowK (spreadW (indCentral[n]! - 22) ^^^ 2 ^ n) = 0) ∧
      (∀ u ∈ (wCert 1).pts.toList, indCentral[22 + u]! < 22 ∧
        red 12 pivK rowK (spreadW u ^^^ 2 ^ indCentral[22 + u]!) = 0) ∧
      (∀ u ∈ (wCert 0).pts.toList, indCentral[22 + u]! = 22 + u) ∧
      (∀ u ∈ (wCert 3).pts.toList, indCentral[22 + u]! = 22 + u) ∧
      (∀ u ∈ (wCert 7).pts.toList, indCentral[22 + u]! = 1046 + sigmaFun u) ∧
      (∀ n ∈ (zCert 0).pts.toList, indCentral[1046 + n]! = 1046 + n) ∧
      (∀ n ∈ (zCert 24).pts.toList, 22 ≤ indCentral[1046 + n]! ∧
        indCentral[1046 + n]! - 22 ∈ (wCert 7).pts.toList ∧
        sigmaFun (indCentral[1046 + n]! - 22) = n) ∧
      (∀ n ∈ (zCert 1).pts.toList, indCentral[1046 + n]! = 1046 + tauFun n) := by
  exact CertificateChecks.Batch3036.central_check_0

end Certificates
