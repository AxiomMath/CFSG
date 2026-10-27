module

public import Certificates.Kernel.C12643.EnumK
public import Certificates.Kernel.Misc.Perm.J2Enum
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.EnumBfsOfOK
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
open CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw keys_of_all all_of_chunks)
open CertificateChecks.KernelMisc.J2En (certL_bound)
open CFSG.KC.EnumBfs (enumOK_enumBfs)

#kc_forall_chunks c12643pt5aS (fun c => c12643pt5a c = true) 5
  CertificateChecks.KernelC12643.c12643pt5a 1
#kc_forall_chunks c12643ky5aS (fun c => c12643ky5a c = true) 5
  CertificateChecks.KernelC12643.c12643ky5a 1
#kc_forall_chunks c12643pt5cS (fun c => c12643pt5c c = true) 1
  CertificateChecks.KernelC12643.c12643pt5c 1
#kc_forall_chunks c12643ky5cS (fun c => c12643ky5c c = true) 1
  CertificateChecks.KernelC12643.c12643ky5c 1
#kc_forall_chunks c12643pt7S (fun c => c12643pt7 c = true) 1
  CertificateChecks.KernelC12643.c12643pt7 1
#kc_forall_chunks c12643ky7S (fun c => c12643ky7 c = true) 1
  CertificateChecks.KernelC12643.c12643ky7 1
#kc_forall_chunks c12643ptES (fun c => c12643ptE c = true) 4
  CertificateChecks.KernelC12643.c12643ptE 1
#kc_forall_chunks c12643kyES (fun c => c12643kyE c = true) 4
  CertificateChecks.KernelC12643.c12643kyE 1
#kc_forall_chunks c12643ptDS (fun c => c12643ptD c = true) 1
  CertificateChecks.KernelC12643.c12643ptD 1
#kc_forall_chunks c12643kyDS (fun c => c12643kyD c = true) 1
  CertificateChecks.KernelC12643.c12643kyD 1
#kc_forall_chunks c12643ptSS (fun c => c12643ptS c = true) 1
  CertificateChecks.KernelC12643.c12643ptS 1
#kc_forall_chunks c12643kySS (fun c => c12643kyS c = true) 1
  CertificateChecks.KernelC12643.c12643kyS 1

theorem g5a_size : gC5a.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem g5c_size : gC5c.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem g7_size : gC7.size = 1 := rfl
theorem gE_size : gCE.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gD_size : gD.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gS5_size : gS5.size = 2 := rfl
theorem ln_size : lineA.size = 6 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem tr_size : transA.size = 6 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem du_size : dUA.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem dv_size : dVA.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem hg5a (k : ℕ) (hk : k < 2) : gC5a[k]! = unpack 315 9 (GC5A k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hg5c (k : ℕ) (hk : k < 2) : gC5c[k]! = unpack 315 9 (GC5C k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hgE (k : ℕ) (hk : k < 2) : gCE[k]! = unpack 315 9 (GCEP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hgD (k : ℕ) (hk : k < 2) : gD[k]! = unpack 315 9 (GDP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hln (k : ℕ) (hk : k < 6) : lineA[k]! = unpack 315 9 (LNP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem htr (k : ℕ) (hk : k < 6) : transA[k]! = unpack 315 9 (TRP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hdu (k : ℕ) (hk : k < 2) : dUA[k]! = unpack 315 9 (DUP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)
theorem hdv (k : ℕ) (hk : k < 2) : dVA[k]! = unpack 315 9 (DVP k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hg7 (k : ℕ) (hk : k < 1) : gC7[k]! = unpack 315 9 (G7 k) := by
  interval_cases k
  exact hx7

theorem hgS5 (k : ℕ) (hk : k < 2) : gS5[k]! = unpack 315 9 (GS5 k) := by
  interval_cases k
  · exact hx5a
  · exact hy2

theorem enum5a : enumOK 315 gC5a keyPts c5aL = true :=
  have b := certL_bound 300 2 C5aP C5aE C5aR C5aL
  enumK_sound (G := GC5A) hw (by decide) g5a_size hg5a b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 60 5 c12643pt5aS) (keys_of_all (all_of_chunks 60 5 c12643ky5aS))

theorem enum5c : enumOK 315 gC5c keyPts c5cL = true :=
  have b := certL_bound 50 2 C5cP C5cE C5cR C5cL
  enumK_sound (G := GC5C) hw (by decide) g5c_size hg5c b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 50 1 c12643pt5cS) (keys_of_all (all_of_chunks 50 1 c12643ky5cS))

theorem enum7 : enumOK 315 gC7 keyPts c7L = true :=
  have b := certL_bound 7 1 C7P C7E C7R C7L
  enumK_sound (G := G7) hw (by decide) g7_size hg7 b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 7 1 c12643pt7S) (keys_of_all (all_of_chunks 7 1 c12643ky7S))

theorem enumE : enumOK 315 gCE keyPts cEL = true :=
  have b := certL_bound 240 2 CEP CEE CER CEL
  enumK_sound (G := GCEP) hw (by decide) gE_size hgE b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 60 4 c12643ptES) (keys_of_all (all_of_chunks 60 4 c12643kyES))

theorem enumD : enumOK 315 gD keyPts cDL = true :=
  have b := certL_bound 60 2 DP DE DR DL
  enumK_sound (G := GDP) hw (by decide) gD_size hgD b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 60 1 c12643ptDS) (keys_of_all (all_of_chunks 60 1 c12643kyDS))

theorem enumS5 : enumOK 315 gS5 keyPts cS5L = true :=
  have b := certL_bound 25 2 S5P S5E S5R S5L
  enumK_sound (G := GS5) hw (by decide) gS5_size hgS5 b.1 b.2.1 b.2.2.1 b.2.2.2 (by quickRfl)
    (all_of_chunks 25 1 c12643ptSS) (keys_of_all (all_of_chunks 25 1 c12643kySS))

theorem size5a : c5aL.pts.size = 300 := (certL_bound 300 2 C5aP C5aE C5aR C5aL).1
theorem size5c : c5cL.pts.size = 50 := (certL_bound 50 2 C5cP C5cE C5cR C5cL).1
theorem size7 : c7L.pts.size = 7 := (certL_bound 7 1 C7P C7E C7R C7L).1
theorem sizeE : cEL.pts.size = 240 := (certL_bound 240 2 CEP CEE CER CEL).1
theorem sizeD : cDL.pts.size = 60 := (certL_bound 60 2 DP DE DR DL).1
theorem sizeS5 : cS5L.pts.size = 25 := (certL_bound 25 2 S5P S5E S5R S5L).1

theorem bfs5a : enumOK 315 gC5a keyPts (c5a ()) = true ∧ (c5a ()).pts.size = 300 := by
  have h := enumOK_enumBfs (fuel := 1000) enum5a (by rw [size5a]; norm_num)
  rw [size5a] at h
  exact h

theorem bfs5c : enumOK 315 gC5c keyPts (c5c ()) = true ∧ (c5c ()).pts.size = 50 := by
  have h := enumOK_enumBfs (fuel := 200) enum5c (by rw [size5c]; norm_num)
  rw [size5c] at h
  exact h

theorem bfs7 : enumOK 315 gC7 keyPts (c7 ()) = true ∧ (c7 ()).pts.size = 7 := by
  have h := enumOK_enumBfs (fuel := 50) enum7 (by rw [size7]; norm_num)
  rw [size7] at h
  exact h

theorem bfsE : enumOK 315 gCE keyPts (cE ()) = true ∧ (cE ()).pts.size = 240 := by
  have h := enumOK_enumBfs (fuel := 800) enumE (by rw [sizeE]; norm_num)
  rw [sizeE] at h
  exact h

theorem bfsD : enumOK 315 gD keyPts (cD ()) = true ∧ (cD ()).pts.size = 60 := by
  have h := enumOK_enumBfs (fuel := 200) enumD (by rw [sizeD]; norm_num)
  rw [sizeD] at h
  exact h

theorem bfsS5 : enumOK 315 gS5 keyPts (cS5 ()) = true ∧ (cS5 ()).pts.size = 25 := by
  have h := enumOK_enumBfs (fuel := 100) enumS5 (by rw [sizeS5]; norm_num)
  rw [sizeS5] at h
  exact h

end CertificateChecks.KernelC12643

end
