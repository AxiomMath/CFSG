module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.SevenInvolutionThreeSwaps

open Equiv

private theorem representative {F : Type*} [Fintype F] [DecidableEq F]
    (e : Fin 6 ↪ F) (k : ℕ) (hk : k ≤ 3) :
    ∃ v ∈ ThreeSwapTwoGroup.subgroup e, v.cycleType = Multiset.replicate k 2 := by
  let t0 := Equiv.swap (e 0) (e 1)
  let t1 := Equiv.swap (e 2) (e 3)
  let t2 := Equiv.swap (e 4) (e 5)
  have hm0 : t0 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t0])
  have hm1 : t1 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t1])
  have hm2 : t2 ∈ ThreeSwapTwoGroup.subgroup e := Subgroup.subset_closure (by simp [t2])
  have hd (i j k l : Fin 6) (h : [i, j, k, l].Nodup) :
      (Equiv.swap (e i) (e j)).Disjoint (Equiv.swap (e k) (e l)) :=
    Perm.disjoint_swap_swap (by simpa only [List.map_cons, List.map_nil] using h.map e.injective)
  have hd01 : t0.Disjoint t1 := hd 0 1 2 3 (by decide)
  have hd02 : t0.Disjoint t2 := hd 0 1 4 5 (by decide)
  have hd12 : t1.Disjoint t2 := hd 2 3 4 5 (by decide)
  have ht (i j : Fin 6) (hij : i ≠ j) : (Equiv.swap (e i) (e j)).cycleType = {2} :=
    Perm.isSwap_iff_cycleType.mp ⟨e i, e j, e.injective.ne hij, rfl⟩
  have ht0 : t0.cycleType = {2} := ht 0 1 (by decide)
  have ht1 : t1.cycleType = {2} := ht 2 3 (by decide)
  have ht2 : t2.cycleType = {2} := ht 4 5 (by decide)
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkcases with rfl | rfl | rfl | rfl
  · exact ⟨1, (ThreeSwapTwoGroup.subgroup e).one_mem, Perm.cycleType_one⟩
  · exact ⟨t0, hm0, ht0⟩
  · refine ⟨t0 * t1, (ThreeSwapTwoGroup.subgroup e).mul_mem hm0 hm1, ?_⟩
    rw [hd01.cycleType_mul, ht0, ht1]
    rfl
  · refine ⟨t0 * t1 * t2,
      (ThreeSwapTwoGroup.subgroup e).mul_mem ((ThreeSwapTwoGroup.subgroup e).mul_mem hm0 hm1) hm2, ?_⟩
    rw [(hd02.mul_left hd12).cycleType_mul, hd01.cycleType_mul, ht0, ht1, ht2]
    rfl

theorem exists_conjugate {F : Type*} [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 7) (e : Fin 6 ↪ F) (u : Perm F) (hu : u ^ 2 = 1) :
    ∃ c : Perm F, c * u * c⁻¹ ∈ ThreeSwapTwoGroup.subgroup e := by
  have htype := Perm.cycleType_of_pow_prime_eq_one hu
  have hsum := u.sum_cycleType_le
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul, hF] at hsum
  norm_num at hsum
  have hk : u.cycleType.card ≤ 3 := by omega
  obtain ⟨v, hv, hvt⟩ := representative e u.cycleType.card hk
  have hconj : IsConj u v := Perm.isConj_of_cycleType_eq (htype.trans hvt.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact ⟨c, hc ▸ hv⟩

end FiveTransitive.SevenInvolutionThreeSwaps

end CFSG
