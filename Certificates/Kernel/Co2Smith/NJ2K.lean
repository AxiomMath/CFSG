module

public import Certificates.Kernel.Co2Smith.NJ1K
public import Certificates.Kernel.Co2Smith.NJ2Data
public import Certificates.Kernel.Co2Smith.RootDefs
public import Certificates.Data.Kernel.Co2Smith.Pts
public import Certificates.Data.Kernel.Co1F2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KS.Co2M
open CertificateChecks.KernelSporSch.Co2M CFSG.KC.Enum

@[expose] noncomputable def jtK (m v : Nat) : Nat := CFSG.KC.M1F2.vmF 22 (CFSG.KC.Co1F2.trK 22 (jcK m)) v

@[expose] noncomputable def vpK : Nat := VG (PV 0) 1

@[expose] noncomputable def njPtAK : Bool :=
  (List.range 3).all (fun k => mapsK (njGK k) 1 1) &&
    (List.range 1024).all (fun m => m == 0 || jtK m vpK != vpK)

@[expose] noncomputable def njPtBK : Bool :=
  glNJPtJ.size == 2300 &&
    (List.range 2300).all (fun x => decide (glNJPtJ[x]! < 1024) &&
      (jtK glNJPtJ[x]! vpK == VG (PV 0) x ||
        (glNJPtJ[x]! != 0 && jtK glNJPtJ[x]! (VG (PV 0) x) == VG (PV 0) x)))

@[expose] noncomputable def njPtCK : Bool :=
  glNJBasis.length == 22 &&
    glNJBasis.all (fun x => decide (x < 2300) && jtK glNJPtJ[x]! vpK == VG (PV 0) x) &&
    glNJBasisInv.size == 22 &&
    CFSG.Sporadic.SmallF2.Native.mulRows 22 (glNJBasis.toArray.map fun x => VG (PV 0) x)
      glNJBasisInv == CFSG.Sporadic.SmallF2.Native.idRows 22

@[expose] noncomputable def njBindK : Bool :=
  allN 3 fun k => bindVK (PV 0) (NJGP k) (CFSG.KC.Co1F2.trK 22 (mulV (jcK glNJTw[k]!) (njGK k)))

@[expose] noncomputable def njO77K : Bool :=
  glNJO77.all (· < 2300) &&
    ((List.range 3).all fun k => glNJO77.all fun x => glNJO77.contains (pg 12 4095 (NJGP k) x)) &&
    glNJO77Wx.size == 1024 && glNJO77Wy.size == 1024 &&
    (List.range 1024).all fun m => m == 0 ||
      (glNJO77.contains glNJO77Wx[m]! && decide (glNJO77Wy[m]! < 2300) &&
        !glNJO77.contains glNJO77Wy[m]! &&
        jtK m (VG (PV 0) glNJO77Wx[m]!) == VG (PV 0) glNJO77Wy[m]!)

theorem njPtA_k : njPtAK = true := by decide +kernel
theorem njPtB_k : njPtBK = true := by
  have key : ∀ (a : Array Nat) (f : Nat → Nat → Bool), (List.range a.size).all
      (fun x => f x a[x]!) = a.toList.zipIdx.all (fun p => f p.2 p.1) := by
    intro a f
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · rintro h ⟨v, i⟩ hm
      rw [List.mem_zipIdx_iff_getElem?] at hm
      obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.1 hm
      simp only at hi hv
      have hi' : i < a.size := by simpa using hi
      have hv' : a[i]! = v := by
        rw [getElem!_pos a i hi', ← hv, Array.getElem_toList]
      have := h i (List.mem_range.2 hi')
      rw [hv'] at this
      exact this
    · intro h x hx
      have hx' := List.mem_range.1 hx
      have hm : (a[x]!, x) ∈ a.toList.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList, getElem?_pos a x hx',
          getElem!_pos a x hx']
      exact h _ hm
  have hs : glNJPtJ.size = 2300 := by decide +kernel
  have h := key glNJPtJ fun x y => decide (y < 1024) &&
    (jtK y vpK == VG (PV 0) x || (y != 0 && jtK y (VG (PV 0) x) == VG (PV 0) x))
  rw [hs] at h
  rw [njPtBK, h]
  decide +kernel
theorem njPtC_k : njPtCK = true := by decide +kernel
theorem njBind_k : njBindK = true := by decide +kernel
theorem njO77_k : njO77K = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
