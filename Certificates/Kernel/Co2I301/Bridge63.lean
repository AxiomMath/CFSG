module

public import Certificates.Kernel.SporSch.Co2M.Six
public import CFSG.Sporadic.Co2I301.Inputs

public section

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.Sporadic.Co2I301
  CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
open CertificateChecks.KernelSporSch.Co2M (PV V_get V_size basis_eq sixIdx_lt sixImage_rep)

@[expose] noncomputable def idxK (k : ℕ) : ℕ := [516, 1588, 1809, 1630, 312, 1801].getD k 0

@[expose] noncomputable def eK (k : ℕ) : ℕ := VG (PV 0) (idxK k) ^^^ VG (PV 0) 29

@[expose] noncomputable def xor6 (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i => if m.testBit i then acc ^^^ f i else acc) 0

@[expose] noncomputable def coordK (x : ℕ) : ℕ :=
  ((List.range 64).find? fun m => xor6 eK m == x).getD 0

@[expose] noncomputable def imgK (A k : ℕ) : ℕ :=
  vmK (VG (PV 0) (idxK k)) A ^^^ vmK (VG (PV 0) 29) A

@[expose] noncomputable def colsOKK (A : ℕ) : Bool :=
  (List.range 6).all fun k => xor6 eK (coordK (imgK A k)) == imgK A k

@[expose] noncomputable def p63K (A p : ℕ) : ℕ := xor6 (fun k => coordK (imgK A k)) (p + 1) - 1

theorem sixIdx_eq (k : ℕ) : sixIdx k = idxK k := by
  unfold sixIdx idxK
  rw [basis_eq.1]

theorem anchor_eq : sixAnchorIdx = 29 := by
  unfold sixAnchorIdx
  exact basis_eq.2

theorem sixPacked_size : sixPacked.size = 6 := by simp [sixPacked]

theorem sixPacked_getK {k : ℕ} (hk : k < 6) : sixPacked[k]! = eK k := by
  have e : sixPacked[k]! = co2PackedVecs[sixIdx k]! ^^^ co2PackedVecs[sixAnchorIdx]! := by
    rw [sixPacked, getElem!_pos _ k (by simpa using hk)]
    simp
  rw [e, V_get (sixIdx_lt k), V_get (by rw [anchor_eq]; norm_num), sixIdx_eq, anchor_eq]
  rfl

theorem foldl_congr_mem' {f g : ℕ → ℕ → ℕ} :
    ∀ (l : List ℕ) (a : ℕ), (∀ acc, ∀ i ∈ l, f acc i = g acc i) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | i :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a i List.mem_cons_self]
    exact foldl_congr_mem' l _ fun acc j hj => h acc j (List.mem_cons_of_mem _ hj)

theorem xor6_congr {f g : ℕ → ℕ} (h : ∀ i < 6, f i = g i) (m : ℕ) : xor6 f m = xor6 g m := by
  unfold xor6
  refine foldl_congr_mem' _ _ fun acc i hi => ?_
  rw [h i (List.mem_range.1 hi)]

theorem xorBits_six {vs : Array ℕ} (hs : vs.size = 6) (m : ℕ) :
    xorBits vs m = xor6 (fun i => vs[i]!) m := by
  rw [xorBits, hs]
  rfl

theorem sixCoord_eq (x : ℕ) : sixCoord x = coordK x := by
  unfold sixCoord coordK
  congr 2
  funext m
  rw [xorBits_six sixPacked_size, xor6_congr fun i hi => sixPacked_getK hi]

theorem sixImage_eq {t : Array ℕ} {A A' : ℕ} (ht : Rep 22 co2PackedVecs t A A') (k : ℕ) :
    sixImage t k = imgK A k := by
  rw [sixImage_rep ht, V_get (sixIdx_lt k), V_get (by rw [anchor_eq]; norm_num), sixIdx_eq,
    anchor_eq, ← vmK_eq, ← vmK_eq]
  rfl

theorem sixCols_size (t : Array ℕ) : (sixCols t).size = 6 := by simp [sixCols]

theorem sixCols_get {t : Array ℕ} {A A' : ℕ} (ht : Rep 22 co2PackedVecs t A A') {k : ℕ}
    (hk : k < 6) : (sixCols t)[k]! = coordK (imgK A k) := by
  rw [sixCols, getElem!_pos _ k (by simpa using hk)]
  simp [sixCoord_eq, sixImage_eq ht]

theorem sixColsOK_eq {t : Array ℕ} {A A' : ℕ} (ht : Rep 22 co2PackedVecs t A A') :
    sixColsOK t = colsOKK A := by
  unfold sixColsOK colsOKK
  rw [Bool.eq_iff_iff, allLt_iff, List.all_eq_true]
  constructor
  · intro h k hk
    have hk' := List.mem_range.1 hk
    have := h k hk'
    rwa [xorBits_six sixPacked_size, xor6_congr fun i hi => sixPacked_getK hi,
      sixCols_get ht hk', sixImage_eq ht] at this
  · intro h k hk
    have := h k (List.mem_range.2 hk)
    rwa [xorBits_six sixPacked_size, xor6_congr fun i hi => sixPacked_getK hi,
      sixCols_get ht hk, sixImage_eq ht]

theorem perm63Of_get {t : Array ℕ} {A A' : ℕ} (ht : Rep 22 co2PackedVecs t A A') {p : ℕ}
    (hp : p < 63) : (perm63Of t)[p]! = p63K A p := by
  unfold perm63Of p63K
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn]
  rw [xorBits_six (sixCols_size t), xor6_congr fun i hi => sixCols_get ht hi]

end CertificateChecks.KernelCo2I301

end
