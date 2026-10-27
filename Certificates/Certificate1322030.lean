module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42Cls
import CFSG.Certificates.Kernel.D42ClsGlue
import CFSG.Certificates.Kernel.Common.ForallTree
import Certificates.Kernel.D42Cls.A
import Certificates.Kernel.D42Cls.B
import Certificates.Certificate8078

namespace CertificateChecks.Batch1322030

open CFSG.KC.D42Cls CFSG.KC.D4PlaneP CFSG.KD.D4Plane CFSG.AGLEmbedding.D4Two

#kc_forall_tree dc3aRowsAll (fun j => rowsOK CFSG.KD.D42A.N CFSG.KD.D42A.T CFSG.KD.D42A.TW
  CFSG.KD.D42A.DP CFSG.KD.D42A.Vm (CFSG.KD.D42A.sW.map (wordP ls)) CFSG.KD.D42A.rows j = true)
  24 CFSG.KD.D42A.dc3arw

#kc_forall_tree dc3aCrAll (fun i => crOK CFSG.KD.D42A.T CFSG.KD.D42A.CR i = true) 8
  CFSG.KD.D42A.dc3acr

#kc_forall_tree dc3aRootsAll (fun j => rootsOK ls (wordP ls CFSG.KD.D42A.kW) CFSG.KD.D42A.Vm
  CFSG.KD.D42A.N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
  (CFSG.KD.D42A.sW.map (wordP ls)) (CFSG.KD.D42A.sW.map fun w => wordP ls w.reverse)
  CFSG.KD.D42A.CR CFSG.KD.D42A.W1 CFSG.KD.D42A.W2 CFSG.KD.D42A.roots j = true) 8
  CFSG.KD.D42A.dc3art

#kc_forall_tree dc3bRowsAll (fun j => rowsOK CFSG.KD.D42B.N CFSG.KD.D42B.T CFSG.KD.D42B.TW
  CFSG.KD.D42B.DP CFSG.KD.D42B.Vm (CFSG.KD.D42B.sW.map (wordP ls)) CFSG.KD.D42B.rows j = true)
  11 CFSG.KD.D42B.dc3brw

#kc_forall_tree dc3bCrAll (fun i => crOK CFSG.KD.D42B.T CFSG.KD.D42B.CR i = true) 8
  CFSG.KD.D42B.dc3bcr

#kc_forall_tree dc3bRootsAll (fun j => rootsOK ls (wordP ls CFSG.KD.D42B.kW) CFSG.KD.D42B.Vm
  CFSG.KD.D42B.N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
  (CFSG.KD.D42B.sW.map (wordP ls)) (CFSG.KD.D42B.sW.map fun w => wordP ls w.reverse)
  CFSG.KD.D42B.CR CFSG.KD.D42B.W1 CFSG.KD.D42B.W2 CFSG.KD.D42B.roots j = true) 38
  CFSG.KD.D42B.dc3brt

theorem hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0 := fun i hi =>
  beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi))

theorem hxy (H : Subgroup CFSG.Quasithin.trialityGroup8) (hx : wE [14, 16, 17] ∈ H)
    (hy : wE [15, 12, 15, 5] ∈ H) : H = ⊤ :=
  eq_top_of_xyOK hL (gxW := [14, 16, 17]) (gyW := [15, 12, 15, 5]) CFSG.KD.D42A.xyOK' H hx hy

theorem nA : CFSG.KD.D42A.n = 139776 := by decide +kernel
theorem NA : CFSG.KD.D42A.N = 1512 := by decide +kernel
theorem nB : CFSG.KD.D42B.n = 326144 := by decide +kernel
theorem NB : CFSG.KD.D42B.N = 648 := by decide +kernel
theorem kWA : CFSG.KD.D42A.kW = CFSG.LocalAnalysis.AGL81I.Section3.D42Over.kAW := by
  decide +kernel
theorem kWB : CFSG.KD.D42B.kW = CFSG.LocalAnalysis.AGL81I.Section3.D42Over.kBW := by
  decide +kernel
theorem lenA : CFSG.KD.D42A.T.length = 24 ∧ CFSG.KD.D42A.TW.length = 24 ∧
    CFSG.KD.D42A.CR.length = 8 ∧ CFSG.KD.D42A.roots.length = 118 := by
  have h := CFSG.KD.D42A.shapeOK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.2, h.2⟩
theorem lenB : CFSG.KD.D42B.T.length = 11 ∧ CFSG.KD.D42B.TW.length = 11 ∧
    CFSG.KD.D42B.CR.length = 8 ∧ CFSG.KD.D42B.roots.length = 600 := by
  have h := CFSG.KD.D42B.shapeOK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.2, h.2⟩

theorem card8078 : Nat.card CFSG.Quasithin.trialityGroup8 = 211341312 :=
  Certificates.certificate8078

theorem gA : Nat.card CFSG.Quasithin.trialityGroup8 = CFSG.KD.D42A.n * CFSG.KD.D42A.N := by
  rw [card8078, nA, NA]

theorem gB : Nat.card CFSG.Quasithin.trialityGroup8 = CFSG.KD.D42B.n * CFSG.KD.D42B.N := by
  rw [card8078, nB, NB]

theorem hNA : CFSG.KD.D42A.N ≤ 64 * 24 := by
  rw [NA]
  norm_num

theorem hNB : CFSG.KD.D42B.N ≤ 64 * 11 := by
  rw [NB]
  norm_num

theorem hMA : CFSG.KD.D42A.roots.length ≤ 16 * 8 := by
  rw [lenA.2.2.2]
  norm_num

theorem hMB : CFSG.KD.D42B.roots.length ≤ 16 * 38 := by
  rw [lenB.2.2.2]
  norm_num

end CertificateChecks.Batch1322030

public section

namespace Certificates

open CertificateChecks.Batch1322030 CFSG.LocalAnalysis.AGL81I.Section3.D42Over

theorem certificate1322030 : CFSG.LocalAnalysis.AGL81I.Section3.D42Over.D42ClsFacts := by
  have classA := CFSG.KC.D42Cls.class_spec hL (m := 24) (M := 8) hNA lenA.1.ge lenA.2.1.ge
    lenA.2.2.1 hMA dc3aRowsAll dc3aCrAll CFSG.KD.D42A.w1OK CFSG.KD.D42A.w2OK dc3aRootsAll
    CFSG.KD.D42A.classOK' hxy gA
  have classB := CFSG.KC.D42Cls.class_spec hL (m := 11) (M := 38) hNB lenB.1.ge lenB.2.1.ge
    lenB.2.2.1 hMB dc3bRowsAll dc3bCrAll CFSG.KD.D42B.w1OK CFSG.KD.D42B.w2OK dc3bRootsAll
    CFSG.KD.D42B.classOK' hxy gB
  have eA : kA = CFSG.KC.D42Cls.wE CFSG.KD.D42A.kW := by rw [kWA]; rfl
  have eB : kB = CFSG.KC.D42Cls.wE CFSG.KD.D42B.kW := by rw [kWB]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eA, classA.1, nA]
  · rw [eB, classB.1, nB]
  · rw [OvergroupConj, eA]
    exact classA.2
  · rw [OvergroupConj, eB]
    exact classB.2

end Certificates
