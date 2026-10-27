module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.QuadraticMap

theorem map_sum_add_of_polar_eq_zero {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N) (s : Finset ι)
    (f : ι → M) (z : M)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0)
    (hz : ∀ i ∈ s, QuadraticMap.polar Q (f i) z = 0) :
    Q (∑ i ∈ s, f i + z) = ∑ i ∈ s, Q (f i) + Q z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have horth' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          QuadraticMap.polar Q (f i) (f j) = 0 :=
        fun i hi j hj hij => horth i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hz' : ∀ i ∈ s, QuadraticMap.polar Q (f i) z = 0 :=
        fun i hi => hz i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, add_assoc, QuadraticMap.map_add Q,
        ih horth' hz', ← QuadraticMap.polarBilin_apply_apply,
        map_add (QuadraticMap.polarBilin Q (f a)),
        map_sum (QuadraticMap.polarBilin Q (f a))]
      have hsum : ∑ i ∈ s, QuadraticMap.polarBilin Q (f a) (f i) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [QuadraticMap.polarBilin_apply_apply]
        exact horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun hai => ha (hai ▸ hi))
      rw [hsum, QuadraticMap.polarBilin_apply_apply,
        hz a (Finset.mem_insert_self a s), add_zero, add_zero, Finset.sum_insert ha]
      abel

theorem map_sum_of_polar_eq_zero {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N) (s : Finset ι)
    (f : ι → M)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0) :
    Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) := by
  simpa using map_sum_add_of_polar_eq_zero Q s f 0 horth
    (fun i _ => by rw [← QuadraticMap.polarBilin_apply_apply]; simp)

end CFSG.QuadraticMap

end
