module

public import Mathlib.GroupTheory.PGroup
public import CFSG.Permutation.FiveTransitive.HallExceptionalCalculation

public section

namespace CFSG

namespace FiveTransitive.Research.HallThreeOrbitExtraction

open MulAction

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_oriented_threeCycle_of_isPGroup_orbit
    (A : Subgroup G) (hA : IsPGroup 3 A)
    (e : Fin 4 ↪ X)
    (hbase : ∀ z : A, ∀ i, (z : G) • e i = e i)
    (p q r : X) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (horbit : MulAction.orbit A p = {p, q, r}) :
    ∃ z : G,
      (∀ i, z • e i = e i) ∧
      z • p = r ∧ z • q = p ∧ z • r = q := by
  have hrmem : r ∈ MulAction.orbit A p := by
    rw [horbit]
    simp
  obtain ⟨z, hzp⟩ := MulAction.mem_orbit_iff.mp hrmem
  have hzrMem : z • r ∈ MulAction.orbit A p :=
    MulAction.mem_orbit_of_mem_orbit z (by rw [horbit]; simp)
  rw [horbit] at hzrMem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzrMem
  have hzr : z • r = q := by
    rcases hzrMem with hzrP | hzrQ | hzrR
    · have htwo : 2 ∣ orderOf z :=
        Research.HallExceptionalCalculation.two_dvd_orderOf_of_smul_swap
          z p r hpr hzp hzrP
      obtain ⟨k, hk⟩ := hA.exists_orderOf_dvd_pow z
      have hoddPow : Odd (3 ^ k) := (show Odd 3 from ⟨1, rfl⟩).pow
      exact (hoddPow.not_two_dvd_nat (htwo.trans hk)).elim
    · exact hzrQ
    · have heq : p = r := (MulAction.injective z) (hzp.trans hzrR.symm)
      exact (hpr heq).elim
  have hzqMem : z • q ∈ MulAction.orbit A p :=
    MulAction.mem_orbit_of_mem_orbit z (by rw [horbit]; simp)
  rw [horbit] at hzqMem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzqMem
  have hzq : z • q = p := by
    rcases hzqMem with hzqP | hzqQ | hzqR
    · exact hzqP
    · have heq : r = q := (MulAction.injective z) (hzr.trans hzqQ.symm)
      exact (hqr heq.symm).elim
    · have heq : p = q := (MulAction.injective z) (hzp.trans hzqR.symm)
      exact (hpq heq).elim
  refine ⟨(z : G), hbase z, ?_, ?_, ?_⟩
  · exact hzp
  · exact hzq
  · exact hzr

end FiveTransitive.Research.HallThreeOrbitExtraction

end CFSG
