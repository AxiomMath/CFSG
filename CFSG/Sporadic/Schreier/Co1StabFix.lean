
module

public import CFSG.Sporadic.Schreier.Co1StabFixBase1

public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Schreier.Co1FullOrbits
public import CFSG.Sporadic.Schreier.Co1Propagate
public import CFSG.Sporadic.Schreier.Co1SplitMono
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_xor toVecD_injective rowsMatrix)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

theorem stabVecOf_mem_X
    {k : ℕ} (hk : k < 4) : stabVecOf k ∈ co1X := by
  have h := stab_x_check
  simp only [Native.stabXCheck, Native.stabXCheckOf, List.all_eq_true, List.mem_range,
    List.any_eq_true, beq_iff_eq] at h
  obtain ⟨i, hi, he⟩ := h k hk
  rw [← gaOrbit_two, show (2 : ℕ) = Native.fullRoot 2 from rfl, gaOrbit_root (by norm_num)]
  exact ⟨i, hi, by rw [stabVecOf, he]⟩

theorem kOrbit_stabH_subset
    {k : ℕ} (hk : k < 4) : kOrbit stabH (stabVecOf k) ⊆ co1X := by
  rw [← gaOrbit_two]
  have hX := stabVecOf_mem_X hk
  rw [← gaOrbit_two] at hX
  rw [← kOrbit_eq_of_mem hX]
  exact kOrbit_mono stabH_le_GA _

theorem ncard_co1X :
    co1X.ncard = 98280 := by
  rw [← gaOrbit_two]
  exact full_orbits_ncard (k := 2) (by norm_num)

theorem co1X_eq_union :
    co1X = kOrbit stabH (stabVecOf 0) ∪ kOrbit stabH (stabVecOf 1) ∪
    kOrbit stabH (stabVecOf 2) ∪ kOrbit stabH (stabVecOf 3) := by
  have hfin : ∀ k, (kOrbit stabH (stabVecOf k)).Finite := fun k =>
    Set.toFinite _
  symm
  refine Set.eq_of_subset_of_ncard_le (Set.union_subset (Set.union_subset (Set.union_subset
    (kOrbit_stabH_subset (by norm_num)) (kOrbit_stabH_subset (by norm_num)))
    (kOrbit_stabH_subset (by norm_num))) (kOrbit_stabH_subset (by norm_num))) ?_ (Set.toFinite _)
  rw [Set.ncard_union_eq _ (((hfin 0).union (hfin 1)).union (hfin 2)) (hfin 3),
    Set.ncard_union_eq _ ((hfin 0).union (hfin 1)) (hfin 2),
    Set.ncard_union_eq (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num))
      (hfin 0) (hfin 1),
    ncard_kOrbit_stabH (by norm_num), ncard_kOrbit_stabH (by norm_num),
    ncard_kOrbit_stabH (by norm_num), ncard_kOrbit_stabH (by norm_num), ncard_co1X]
  · rfl
  · exact Disjoint.union_left (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num))
      (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num))
  · exact Disjoint.union_left (Disjoint.union_left
      (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num))
      (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num)))
      (kOrbit_stabH_disjoint (by norm_num) (by norm_num) (by norm_num))

theorem two_point_stabilizer_fixed_vector_spaces :
    stabVecOf 0 = toVecD 24 16663704 ∧ stabVecOf 1 = toVecD 24 6009710 ∧
    stabVecOf 2 = toVecD 24 769771 ∧ stabVecOf 3 = toVecD 24 6244414 ∧
    stabVecOf 0 + stabVecOf 3 = toVecD 24 10554534 ∧
    (∀ k < 4, stabVecOf k ∈ co1X) ∧
    co1X = kOrbit stabH (stabVecOf 0) ∪ kOrbit stabH (stabVecOf 1) ∪
      kOrbit stabH (stabVecOf 2) ∪ kOrbit stabH (stabVecOf 3) ∧
    (∀ j k, j < 4 → k < 4 → j ≠ k →
      Disjoint (kOrbit stabH (stabVecOf j)) (kOrbit stabH (stabVecOf k))) ∧
    kOrbit stabH (stabVecOf 0) = {stabVecOf 0} ∧
    (kOrbit stabH (stabVecOf 1)).ncard = 46575 ∧ (kOrbit stabH (stabVecOf 2)).ncard = 47104 ∧
    (kOrbit stabH (stabVecOf 3)).ncard = 4600 ∧
    (∀ j ∈ ({1, 2, 3} : Finset ℕ),
      fixSpace (stabVecOf j) = ↑(Submodule.span (ZMod 2) {stabVecOf 0, stabVecOf j})) ∧
    fixPts (stabVecOf 1) = {stabVecOf 1} ∧ fixPts (stabVecOf 2) = {stabVecOf 2} ∧
    fixPts (stabVecOf 3) = {stabVecOf 3, stabVecOf 0 + stabVecOf 3} := by
  refine ⟨rfl, rfl, rfl, rfl, by rw [stabVecOf, stabVecOf, ← toVecD_xor]; rfl,
    fun k hk => stabVecOf_mem_X hk, co1X_eq_union,
    fun j k hj hk hjk => kOrbit_stabH_disjoint hj hk hjk, kOrbit_stabH_zero,
    ncard_kOrbit_stabH (k := 1) (by norm_num), ncard_kOrbit_stabH (k := 2) (by norm_num),
    ncard_kOrbit_stabH (k := 3) (by norm_num), fun j hj => ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    exacts [fixSpace_eq (m := 0) (by norm_num), fixSpace_eq (m := 1) (by norm_num),
      fixSpace_eq (m := 2) (by norm_num)]
  · have h := fixPts_eq (m := 0) (by norm_num)
    simp only [show (0 : ℕ) ≠ 2 by norm_num, ↓reduceIte] at h
    exact h
  · have h := fixPts_eq (m := 1) (by norm_num)
    simp only [show (1 : ℕ) ≠ 2 by norm_num, ↓reduceIte] at h
    exact h
  · have h := fixPts_eq (m := 2) (by norm_num)
    simp only [↓reduceIte] at h
    exact h

end CFSG.Sporadic.Co1Schreier
