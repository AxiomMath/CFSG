module

public import CFSG.Quasithin.H13.NQCatJ4Native
public import CFSG.Sporadic.HS.SmallF2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin.H13.NQCat.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open Matrix

theorem rrefOK_spec {d : ℕ} {A : Array (ℕ × ℕ)} (h : rrefOK d A = true) :
    (∀ (i : ℕ) (hi : i < A.size), A[i].1 < d ∧ A[i].2.testBit A[i].1 = true) ∧
      ∀ (i : ℕ) (hi : i < A.size) (j : ℕ) (hj : j < A.size), i ≠ j →
        A[j].2.testBit A[i].1 = false := by
  unfold rrefOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  refine ⟨fun i hi => h.1 i hi, fun i hi j hj hij => ?_⟩
  rcases h.2 i hi j hj with h' | h'
  · exact absurd h' hij
  · rwa [getElem!_pos A j hj, getElem!_pos A i hi] at h'

theorem linearIndependent_of_rrefOK {d : ℕ} {A : Array (ℕ × ℕ)} (h : rrefOK d A = true) :
    LinearIndependent (ZMod 2) fun i : Fin A.size => toVecD d A[i.val].2 := by
  obtain ⟨h1, h2⟩ := rrefOK_spec h
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨hpd, hbit⟩ := h1 i.val i.isLt
  have hc := congrFun hg ⟨A[i.val].1, hpd⟩
  rw [Finset.sum_apply, Finset.sum_eq_single i] at hc
  · simpa [toVecD_apply, hbit] using hc
  · intro j _ hji
    have := h2 i.val i.isLt j.val j.isLt (fun e => hji (Fin.ext e.symm))
    simp [toVecD_apply, this]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem toVecD_colFixT (d : ℕ) (M : Array ℕ) (v : ℕ) :
    toVecD d (colFixT d (transposeRows d M) v) = (rowsMatrix d M - 1) *ᵥ toVecD d v := by
  rw [colFixT, toVecD_xor, ← rowsMatrix_mulVec, sub_mulVec, one_mulVec]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply]
  generalize (rowsMatrix d M *ᵥ toVecD d v) j = a
  generalize toVecD d v j = b
  revert a b
  decide

theorem finrank_ker_of_fixCertOK {d : ℕ} {M : Array ℕ} {K : Array (ℕ × ℕ)}
    {I : Array (ℕ × ℕ × ℕ)} {k : ℕ} (h : fixCertOK d (transposeRows d M) K I k = true) :
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (rowsMatrix d M - 1))) = k := by
  unfold fixCertOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hK, hKker⟩, hI⟩, hk⟩, hsum⟩ := h
  set N := Matrix.mulVecLin (rowsMatrix d M - 1)
  have hKmem : ∀ i : Fin K.size, toVecD d K[i.val].2 ∈ LinearMap.ker N := by
    intro i
    have := (Array.all_eq_true.1 hKker) i.val i.isLt
    simp only [beq_iff_eq] at this
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← toVecD_colFixT, this, toVecD_zero]
  have hKind : LinearIndependent (ZMod 2) fun i : Fin K.size =>
      (⟨toVecD d K[i.val].2, hKmem i⟩ : LinearMap.ker N) :=
    LinearIndependent.of_comp (LinearMap.ker N).subtype (linearIndependent_of_rrefOK hK)
  have hKle := hKind.fintype_card_le_finrank
  set I' := I.map fun e => (e.1, colFixT d (transposeRows d M) e.2.2) with hI'
  have hI'size : I'.size = I.size := Array.size_map ..
  have hImem : ∀ i : Fin I'.size, toVecD d I'[i.val].2 ∈ LinearMap.range N := by
    intro i
    have hi : i.val < I.size := hI'size ▸ i.isLt
    refine ⟨toVecD d I[i.val].2.2, ?_⟩
    rw [Matrix.mulVecLin_apply, ← toVecD_colFixT]
    simp [hI']
  have hIind : LinearIndependent (ZMod 2) fun i : Fin I'.size =>
      (⟨toVecD d I'[i.val].2, hImem i⟩ : LinearMap.range N) :=
    LinearIndependent.of_comp (LinearMap.range N).subtype (linearIndependent_of_rrefOK hI)
  have hIle := hIind.fintype_card_le_finrank
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fin_fun] at hrn
  simp only [Fintype.card_fin] at hKle hIle
  rw [hI'size] at hIle
  omega

theorem finrank_ker_of_fixDimOK {d : ℕ} {M : Array ℕ} {k : ℕ} (h : fixDimOK d M k = true) :
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (rowsMatrix d M - 1))) = k :=
  finrank_ker_of_fixCertOK h

end CFSG.Quasithin.H13.NQCat
