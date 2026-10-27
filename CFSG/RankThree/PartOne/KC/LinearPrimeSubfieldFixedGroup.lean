module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open KCLinearSubfield

theorem higher_linear_prime_subfield_fixed_group_and_full_centralizer {ℓ p f n : ℕ}
    (hℓ : ℓ.Prime) (_hp : p.Prime) (_hpℓ : p ≠ ℓ) (_hf : 1 ≤ f) (hn : 3 ≤ n)
    (hnp : Nat.Coprime n p) {K : Type*} [Field K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    Function.Injective (linearSubfieldInclusion n (semilinearFixedSubfield σ)) ∧
      {x : projectiveSL n K | fieldAut n K σ x = x} =
        ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
          Set (projectiveSL n K)) ∧
      fixingSubgroup (MulAut (projectiveSL n K))
          ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
            Set (projectiveSL n K)) = zpowers (fieldAut n K σ) ∧
      IsCyclic (zpowers (fieldAut n K σ)) ∧ Nat.card (zpowers (fieldAut n K σ)) = p := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  refine ⟨linearSubfieldInclusion_injective (by omega) _,
    fixed_points_eq_range hk (by omega) (root_descent_of_coprime hk hσp hnp),
    fixingSubgroup_range_linearSubfieldInclusion hk hn, inferInstance, ?_⟩
  rw [Nat.card_zpowers, orderOf_fieldAut hn, hσ]

end CFSG.RankThree.PartOne
