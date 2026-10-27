module

public import CFSG.CGT.M24R.M24NativeInputs
import CFSG.Certificates.Kernel.J2ModelKSound

public section

namespace CertificateChecks.Batch21191

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.KGC31P CFSG.KC.J2ModelK
  CFSG.CGT.M24R CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu.Native
open CFSG.KC.Child3 (tabP)

private def pA : Nat := 817395973838868159142633316802379971

private def pB : Nat := 938078705133617800621527216201835139

private noncomputable def gAB (z : ℤ) : Nat := if z = 1 then pA else if z = 2 then pB else pidn 24 5

private noncomputable def pImg (k : Nat) : Nat := pword 24 5 gAB (m24GenWord k)

private noncomputable def gL (z : ℤ) : Nat :=
  if 0 < z then pImg (z - 1).toNat else pinv 24 5 (pImg (-z - 1).toNat)

private theorem hsz : szOK 24 5 = true := by decide +kernel

private theorem ppA : PP 24 5 pA := PP_of_permOK hsz (by decide +kernel)

private theorem ppB : PP 24 5 pB := PP_of_permOK hsz (by decide +kernel)

private theorem tA_eq : (m24Data ()).tA = tabP 24 5 pA := by decide +kernel

private theorem tB_eq : (m24Data ()).tB = tabP 24 5 pB := by decide +kernel

private theorem ppAB (z : ℤ) : PP 24 5 (gAB z) := by
  unfold gAB
  split_ifs
  · exact ppA
  · exact ppB
  · exact PP.id hsz

private theorem hAB (z : ℤ) : m24AB z = tabP 24 5 (gAB z) := by
  unfold m24AB gAB
  split_ifs
  · exact tA_eq
  · exact tB_eq
  · exact idT_tabP hsz

private theorem img_eq (k : Nat) : m24Img k = tabP 24 5 (pImg k) := wordT_tabP hsz hAB ppAB _

private theorem ppImg (k : Nat) : PP 24 5 (pImg k) := PP_pword hsz ppAB _

private theorem hL (z : ℤ) : m24L z = tabP 24 5 (gL z) := by
  unfold m24L gL
  split_ifs
  · exact img_eq _
  · rw [img_eq, invT_tabP (ppImg _)]

private theorem ppL (z : ℤ) : PP 24 5 (gL z) := by
  unfold gL
  split_ifs
  · exact ppImg _
  · exact (ppImg _).pinv

private theorem m24TabCheck_0 : m24TabCheck = true := by
  unfold m24TabCheck
  have e1 : (List.range 11).all (fun k => m24Img k == genTable k &&
      invOK 24 (m24Img k) (invT 24 (m24Img k))) =
      (List.range 11).all (fun k => tabP 24 5 (pImg k) == genTable k) :=
    all_congr' fun k _ => by rw [img_eq, invOK_tabP (ppImg k), Bool.and_true]
  have e2 : m24Rels.all (fun r => wordT 24 m24L (r.map letterZ) == idT 24) =
      m24Rels.all (fun r => Nat.beq (pword 24 5 gL (r.map letterZ)) (pidn 24 5)) :=
    all_congr' fun r _ => by
      rw [wordT_tabP hsz hL ppL, idT_tabP hsz, beq_tabP (PP_pword hsz ppL _) (PP.id hsz)]
  rw [e1, e2, wordT_tabP hsz hL ppL, wordT_tabP hsz hL ppL, tA_eq, tB_eq,
    beq_tabP (PP_pword hsz ppL _) ppA, beq_tabP (PP_pword hsz ppL _) ppB]
  decide +kernel

end CertificateChecks.Batch21191

namespace Certificates

open CertificateChecks

open CFSG.CGT.M24R in
theorem certificate21191 : m24TabCheck = true := CertificateChecks.Batch21191.m24TabCheck_0

end Certificates
