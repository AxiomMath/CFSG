module

public import Certificates.Kernel.Co1P.PinEChkHs
public import Certificates.Kernel.Co1P.PinEChkHis
public import Certificates.Kernel.Co1P.PinEChkKey
public import Certificates.Kernel.Co1P.Bray
public import Certificates.Kernel.Co1P.Chk21157
public import CFSG.Certificates.Kernel.Co1PPinSound
public import Certificates.Kernel.Co1P.Trees

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native

theorem hsE_pin : ∀ i < 12600, pinAt (hsAct BK) oneK hsE recE i = true :=
  chunks_all (f := pinAt (hsAct BK) oneK hsE recE) (N := 12600) (nc := 197) (by decide)
    fun c hc => HsE.all c hc

theorem hisE_pin : ∀ i < 12600, pinAt (hisAct BIK) oneK hisE recE i = true :=
  chunks_all (f := pinAt (hisAct BIK) oneK hisE recE) (N := 12600) (nc := 197) (by decide)
    fun c hc => HisE.all c hc

theorem keyE_all : ∀ s < 12600, keyAt 12600 64 skE ixE ptPE s = true :=
  chunks_all (f := keyAt 12600 64 skE ixE ptPE) (N := 12600) (nc := 197) (by decide)
    fun c hc => KeyE.all c hc

theorem hsE_walk {i : Nat} (hi : i < 12600) : hsE i = hsW orbEMasks i :=
  pin_walk (brayTree_parts treeE_ok).1 recsE_pin (by rw [recsE_len]; exact hsE_pin) i
    (by rw [recsE_len]; exact hi)

theorem hisE_walk {i : Nat} (hi : i < 12600) : hisE i = hisW orbEMasks i :=
  pin_walk (brayTree_parts treeE_ok).2 recsE_pin (by rw [recsE_len]; exact hisE_pin) i
    (by rw [recsE_len]; exact hi)

theorem ptPE_eq {i : Nat} (hi : i < 12600) : ptPE i = ptE i := by
  unfold ptPE ptE
  rw [hsE_walk hi, hisE_walk hi]

theorem orbE_pt' {k : Nat} (hk : k < 12600) : orbE.c.pts[k]! = unpackR 24 (ptPE k) := by
  have hj : k < (recsT orbEMasks).length + 1 := by rw [recsE_len]; omega
  rw [orbE_eq, ptPE_eq hk]
  exact bray_pts treeE_ok _ hj

theorem orbE_hs' {k : Nat} (hk : k < 12600) : orbE.hs[k]! = unpackR 24 (hsE k) := by
  have hj : k < (recsT orbEMasks).length + 1 := by rw [recsE_len]; omega
  rw [orbE_eq, hsE_walk hk]
  exact bray_hs treeE_ok _ hj

theorem orbE_his' {k : Nat} (hk : k < 12600) : orbE.his[k]! = unpackR 24 (hisE k) := by
  have hj : k < (recsT orbEMasks).length + 1 := by rw [recsE_len]; omega
  rw [orbE_eq, hisE_walk hk]
  exact bray_his treeE_ok _ hj

theorem orbE_size' : orbE.c.pts.size = 12600 := by
  rw [orbE_eq, treeT_eq, mkOrbT_size, recsE_len]

theorem memE_iff (X : Nat) : memE X = true ↔ ∃ i < 12600, eqK X (ptPE i) = true :=
  memPin_iff keyE_all (by decide) (by decide) X

theorem orbE_mem (X : Nat) : (ptSet orbE).contains (unpackR 24 X) = memE X := by
  apply Bool.eq_iff_iff.2
  rw [memE_iff, ptSet, Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff,
    Array.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [orbE_size'] at hk
    refine ⟨k, hk, ?_⟩
    rw [← getElem!_pos orbE.c.pts k (by rw [orbE_size']; exact hk), orbE_pt' hk] at e
    rw [← beq_unpack, e]
    exact beq_self_eq_true _
  · rintro ⟨k, hk, e⟩
    refine ⟨k, by rw [orbE_size']; exact hk, ?_⟩
    rw [← getElem!_pos orbE.c.pts k (by rw [orbE_size']; exact hk), orbE_pt' hk]
    have e' : (unpackR 24 X == unpackR 24 (ptPE k)) = true := by
      rw [beq_unpack]
      exact e
    exact (beq_iff_eq.1 e').symm

end CertificateChecks.KernelCo1P

end
