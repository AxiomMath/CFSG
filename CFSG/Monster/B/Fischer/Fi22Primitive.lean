module

public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Monster.B.Fischer.Fi22PrimitiveCheck
public import CFSG.Certificates.MergePrimitivity

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2

theorem fi22StabIdx_eq :
    fi22StabIdx = (List.range 19).filter fun j => decide (fi22StrongPerm j 0 = 0) :=
  fi22Primitive_check.1

theorem mem_fi22StabIdx
    {j : ℕ} (hj : j ∈ fi22StabIdx) : j < 19 ∧ fi22StrongPerm j 0 = 0 := by
  rw [fi22StabIdx_eq, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
  exact hj

theorem fi22H0_fix :
    ∀ h ∈ fi22H0, h 0 = 0 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact (mem_fi22StabIdx hj).2
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem fi22H0_le :
    fi22H0 ≤ fi22P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (0 : Fin 3510) := by
  rw [fi22H0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj19 := (mem_fi22StabIdx hj).1
  refine ⟨?_, MulAction.mem_stabilizer_iff.2 ?_⟩
  · have h := fi22Chain_strong_mem ⟨j, hj19⟩
    rw [fi22Chain_strong_get] at h
    exact h
  · rw [Equiv.Perm.smul_def]
    exact (mem_fi22StabIdx hj).2

theorem fi22StabOrbit_eq
    {t : ℕ} (ht : t < 3) :
    {y : Fin 3510 | (y : ℕ) ∈ fi22StabOrbit t} =
      MulAction.orbit fi22H0 (fi22Pt ((fi22StabOrbit t).headD 0)) :=
  fi22Primitive_check.2.1 t ht

theorem fi22StabOrbit_cover
    (y : Fin 3510) : ∃ t < 3, (y : ℕ) ∈ fi22StabOrbit t :=
  fi22Primitive_check.2.2.1 y

theorem fi22StabOrbit_heads :
    ((List.range 3).map fun t => (fi22StabOrbit t).headD 0) = [0, 1, 11] :=
  fi22Primitive_check.2.2.2.1

theorem fi22StabOrbit_zero :
    fi22StabOrbit 0 = [0] := by
  have hlen : (fi22StabOrbit 0).length = 1 := by
    have := CERT_Fi22_matrix_action_data.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [show List.range 3 = [0, 1, 2] from rfl] at this
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at this
    exact this.1
  have hhead : (fi22StabOrbit 0).headD 0 = 0 := by
    have := fi22StabOrbit_heads
    rw [show List.range 3 = [0, 1, 2] from rfl] at this
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at this
    exact this.1
  match h : fi22StabOrbit 0, hlen with
  | [a], _ => rw [h] at hhead; simp only [List.headD_cons] at hhead; rw [hhead]

theorem fi22Merge_one :
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 1) (fi22MergeList 0) :=
  fi22Primitive_check.2.2.2.2.1

theorem fi22Merge_eleven :
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 11) (fi22MergeList 1) :=
  fi22Primitive_check.2.2.2.2.2

theorem fi22P_primitive :
    MulAction.IsPreprimitive fi22P (Fin 3510) := by
  have hP := fi22P_eq
  have htrans : MulAction.IsPretransitive
      (Subgroup.closure (Set.range fun k : Fin 2 => fi22GenPerm k)) (Fin 3510) :=
    hP ▸ fi22P_transitive
  have key := stabilizer_orbit_merge_primitivity (fun k : Fin 2 => fi22GenPerm k) 0 fi22H0
    (hP ▸ fun h hh => (fi22H0_le hh).1) fi22H0_fix (xs := ![fi22Pt 1, fi22Pt 11]) ?_ ?_
  · exact hP ▸ key
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := fi22StabOrbit_cover x
    have hmem := (Set.ext_iff.1 (fi22StabOrbit_eq ht) x).1 hxt
    have hheads := fi22StabOrbit_heads
    rw [show List.range 3 = [0, 1, 2] from rfl] at hheads
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hheads
    obtain ⟨h0, h1, h2, -⟩ := hheads
    interval_cases t
    · exfalso
      rw [fi22StabOrbit_zero, List.mem_singleton] at hxt
      exact hx (Fin.ext hxt)
    · rw [h1] at hmem
      obtain ⟨⟨g, hg⟩, rfl⟩ := hmem
      exact ⟨0, g, hg, rfl⟩
    · rw [h2] at hmem
      obtain ⟨⟨g, hg⟩, rfl⟩ := hmem
      exact ⟨1, g, hg, rfl⟩
  · intro j
    fin_cases j
    · exact ⟨_, fi22Merge_one⟩
    · exact ⟨_, fi22Merge_eleven⟩

end CFSG.Monster.B.Fischer
