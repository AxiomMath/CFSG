module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin.SteinbergBT

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a

variable {r : ℕ} {K : Type} [Field K]

theorem sl2Up_mul_sl2Low_props [CharP K 2] :
    ((sl2Up K 1 * sl2Low K (-1) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      0 ∧ (sl2Up K 1 * sl2Low K (-1)) ^ 3 = 1 := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  refine ⟨?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [sl2Up, sl2Low, Matrix.mul_apply, Fin.sum_univ_two]
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [sl2Up, sl2Low, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      exact hneg

theorem exists_weylRep_eq_mul_orderOf_eq_three [CharP K 2] (k : Fin r) :
    ∃ x y : StatedSp r K, x ∈ unipotent r K ∧ weylRep K k = x * y * x ∧ orderOf (x * y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hm0, hm3⟩ := sl2Up_mul_sl2Low_props (K := K)
  set m := sl2Up K 1 * sl2Low K (-1) with hm
  have hxU : pairRootElt (inl_ne_simpleSnd k) (1 : K) ∈ unipotent r K := by
    refine rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k) ?_
    rw [← rootVec_simpleSnd]
    exact pairRootElt_mem_rootSubgroup _ _
  refine ⟨pairRootElt (inl_ne_simpleSnd k) 1, pairRootElt (inl_ne_simpleSnd k).symm (-1), hxU,
    rfl, ?_⟩
  by_cases h : (k : ℕ) + 1 < r
  · set k' : Fin r := ⟨k + 1, h⟩
    have hkk' : k ≠ k' := fun e => by
      have := congrArg Fin.val e
      simp [k'] at this
    have hsnd : simpleSnd k = Sum.inl k' := by
      unfold simpleSnd
      rw [dite_eq_left h]
    have e : pairRootElt (inl_ne_simpleSnd k) (1 : K) * pairRootElt (inl_ne_simpleSnd k).symm (-1) =
        rho k k' hkk' m := by
      have e1 := weylRep_eq_pair (K := K) k hsnd (fun e => hkk' (Sum.inl_injective e))
      have e2 : ∀ {b : Fin r ⊕ Fin r} (hb : simpleSnd k = b) (hkb : Sum.inl k ≠ b),
          pairRootElt (inl_ne_simpleSnd k) (1 : K) * pairRootElt (inl_ne_simpleSnd k).symm (-1) =
            pairRootElt hkb 1 * pairRootElt hkb.symm (-1) := by
        intro b hb hkb
        subst hb
        rfl
      rw [e2 hsnd (fun e => hkk' (Sum.inl_injective e)), pairRootElt_short hkk',
        pairRootElt_short' hkk', ← map_mul]
    rw [e]
    refine orderOf_eq_prime (by rw [← map_pow, hm3, map_one]) fun h1 => ?_
    have h2 := congrArg (fun g : StatedSp r K =>
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl k) (Sum.inl k)) h1
    simp only [coe_rho', fromBlocks_apply₁₁, pairMat_apply_fst, ite_true] at h2
    rw [hm0] at h2
    simp at h2
  · have hsnd : simpleSnd k = Sum.inr k := by
      unfold simpleSnd
      rw [dite_eq_right h]
    have e : pairRootElt (inl_ne_simpleSnd k) (1 : K) * pairRootElt (inl_ne_simpleSnd k).symm (-1) =
        lam k m := by
      have e2 : ∀ {b : Fin r ⊕ Fin r} (hb : simpleSnd k = b) (hkb : Sum.inl k ≠ b),
          pairRootElt (inl_ne_simpleSnd k) (1 : K) * pairRootElt (inl_ne_simpleSnd k).symm (-1) =
            pairRootElt hkb 1 * pairRootElt hkb.symm (-1) := by
        intro b hb hkb
        subst hb
        rfl
      rw [e2 hsnd Sum.inl_ne_inr, pairRootElt_long, pairRootElt_long', ← map_mul]
    rw [e]
    refine orderOf_eq_prime (by rw [← map_pow, hm3, map_one]) fun h1 => ?_
    have h2 := congrArg (fun g : StatedSp r K =>
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl k) (Sum.inl k)) h1
    simp only [coe_lam, pairMat_apply_fst, ite_true] at h2
    rw [hm0] at h2
    simp at h2

theorem even_symplectic_three_free_sylow_overgroups_are_triangular [Finite K] [CharP K 2] :
    (∀ H : Subgroup (StatedSp r K), unipotent r K ≤ H → ¬3 ∣ Nat.card H → H ≤ borelSubgroup r K) ∧
      Subgroup.normalizer (unipotent r K : Set (StatedSp r K)) = borelSubgroup r K := by
  refine ⟨fun H hUH h3 g hg => ?_, normalizer_unipotent⟩
  have hn : ∀ k : Fin r, weylRep K k ∉ H := by
    intro k hk
    obtain ⟨x, y, hxU, hxy, hord⟩ := exists_weylRep_eq_mul_orderOf_eq_three (K := K) k
    have hxH : x ∈ H := hUH hxU
    have hyH : y ∈ H := by
      have e : y = x⁻¹ * weylRep K k * x⁻¹ := by
        rw [hxy]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hxH) hk) (inv_mem hxH)
    exact h3 (hord ▸ Subgroup.orderOf_dvd_natCard H (mul_mem hxH hyH))
  have hQ := le_flagStabilizer_borelCuts H hUH hg
  refine mem_borelSubgroup.2 fun i hi1 hir => ?_
  refine mem_flagStabilizer.1 hQ i ⟨⟨i - 1, by omega⟩, by simp; omega, hn _⟩

end CFSG.Quasithin.SteinbergBT
