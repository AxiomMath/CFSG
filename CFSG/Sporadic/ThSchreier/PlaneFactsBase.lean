
module

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public import CFSG.Sporadic.Th.SimpleBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def CanonRows (P : Set RowV) (m₁ m₂ : ℕ) : Prop :=
  ∃ m₃ : ℕ, 0 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧ m₃ < 2 ^ 248 ∧
    toRow (rowOfNat m₃) = toRow (rowOfNat m₁) + toRow (rowOfNat m₂) ∧
    P = {0, toRow (rowOfNat m₁), toRow (rowOfNat m₂), toRow (rowOfNat m₃)}

theorem canonRows_of_isCanonical {k : Key} (hk : k.isCanonical = true) :
    CanonRows (rowPlane k) k.u.toNat k.v.toNat := by
  obtain ⟨hu, hv, hu0, huv, hvs⟩ := Key.isCanonical_iff.1 hk
  refine ⟨(k.u.xor k.v).toNat, ?_, huv, hvs, (V4.wf_iff_toNat_lt _).1 (V4.xor_wf hu hv), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k.u.toNat with h | h
    · exact absurd (V4.toNat_eq_zero.1 h) hu0
    · exact h
  · rw [← toVec_eq_rowOfNat, ← toVec_eq_rowOfNat, ← toVec_eq_rowOfNat, V4.toVec_xor]
    rfl
  · rw [rowPlane, ← toVec_eq_rowOfNat, ← toVec_eq_rowOfNat, ← toVec_eq_rowOfNat, V4.toVec_xor]
    rfl

theorem pairwise_lt_of_succ {l : List ℕ}
    (h : ∀ k (hk : k + 1 < l.length), l[k]'(by omega) < l[k + 1]) :
    l.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  induction j with
  | zero => omega
  | succ j ih =>
    have hs : l[j] < l[j + 1] := h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact (ih (by omega) h').trans hs
    · subst h'
      exact hs

theorem mem_of_card_eq {n : ℕ} {p : ℕ → Prop} [DecidablePred p] {l : List ℕ}
    (hl : l.Pairwise (· < ·)) (hmem : ∀ x ∈ l, x < n ∧ p x)
    (hcard : ((Finset.range n).filter p).card = l.length) {x : ℕ} (hx : x < n) (hpx : p x) :
    x ∈ l := by
  have hnd : l.Nodup := hl.imp ne_of_lt
  have hsub : l.toFinset ⊆ (Finset.range n).filter p := by
    intro y hy
    rw [List.mem_toFinset] at hy
    rw [Finset.mem_filter, Finset.mem_range]
    exact hmem y hy
  have heq : l.toFinset = (Finset.range n).filter p := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard, List.toFinset_card_of_nodup hnd]
  have hmx : x ∈ (Finset.range n).filter p := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, hpx⟩
  rw [← heq, List.mem_toFinset] at hmx
  exact hmx

theorem ncard_fin_mem {n : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    {i : Fin n | i.val ∈ l}.ncard = l.length := by
  rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun i _ => i.val)
  · intro i hi
    simpa using hi
  · intro i j _ _ h
    exact Fin.ext h
  · intro x hx
    rw [Finset.mem_coe, List.mem_toFinset] at hx
    exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩

theorem getElem!_toArray_eq {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    l.toArray[k]! = l[k] := by
  rw [getElem!_pos l.toArray k (by simpa using hk), List.getElem_toArray]

theorem centImageKeys_getElem {k : ℕ} (hk : k < 120) :
    centImageKeys[k]! = ⟨v4OfNat (centImageRows.getD (2 * k) 0),
      v4OfNat (centImageRows.getD (2 * k + 1) 0)⟩ := by
  rw [getElem!_pos centImageKeys k (by simp [centImageKeys, hk])]
  simp [centImageKeys]

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF hS

omit hF in
theorem centFixed_sorted : centFixedIdx.Pairwise (· < ·) := by
  refine pairwise_lt_of_succ fun k hk => ?_
  have h := ScanFacts.fixedSorted hS k (by simpa [centFixedArr] using hk)
  rwa [show centFixedArr = centFixedIdx.toArray from rfl,
    getElem!_toArray_eq (by omega : k < centFixedIdx.length), getElem!_toArray_eq hk] at h

omit hF in
theorem centFixed_mem {x : ℕ} (hx : x ∈ centFixedIdx) : x < nX ∧ αIdx x = x := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have h := ScanFacts.fixedMem hS k (by simpa [centFixedArr] using hk)
  rw [show centFixedArr[k]! = centFixedIdx[k] from getElem!_toArray_eq hk] at h
  exact h

omit hF in
theorem fixed_iff_mem {i : ℕ} (hi : i < nX) : αIdx i = i ↔ i ∈ centFixedIdx := by
  constructor
  · intro h
    classical
    refine mem_of_card_eq (n := nX) (p := fun i => αIdx i = i) (centFixed_sorted hS)
      (fun x hx => centFixed_mem hS hx) ?_ hi h
    have h1 := ScanFacts.fixedCount hS
    simpa [centFixedArr] using h1
  · intro h
    exact (centFixed_mem hS h).2

omit hF in
theorem centImage_sorted : centImageIdx.Pairwise (· < ·) := by
  refine pairwise_lt_of_succ fun k hk => ?_
  have h := ScanFacts.imageSorted hS k (by simpa [centImageArr] using hk)
  rwa [show centImageArr = centImageIdx.toArray from rfl,
    getElem!_toArray_eq (by omega : k < centImageIdx.length), getElem!_toArray_eq hk] at h

omit hF in
theorem centImage_mem {k : ℕ} (hk : k < centImageIdx.length) :
    centImageIdx[k] < nX ∧
      rowKeyOf (readKey thSt.keys centImageIdx[k]) = centImageKeys[k]! ∧
      inUA (centImageKeys[k]!).u = true ∧ inUA (centImageKeys[k]!).v = true := by
  have h := ScanFacts.imageMem hS k (by simpa [centImageArr] using hk)
  rw [show centImageArr[k]! = centImageIdx[k] from getElem!_toArray_eq hk] at h
  exact h

end Facts

end CFSG.Sporadic.ThSchreier
