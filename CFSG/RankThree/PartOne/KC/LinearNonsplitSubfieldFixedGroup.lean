module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open KCLinearSubfield

theorem nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer {ℓ p f n : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (_hp3 : 3 < p) (_hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hn : 3 ≤ n)
    {K : Type*} [Field K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hpq : ¬ p ∣ ℓ ^ f - 1)
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    (p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p)) ∧
      Function.Injective (linearSubfieldInclusion n (semilinearFixedSubfield σ)) ∧
      {x : projectiveSL n K | fieldAut n K σ x = x} =
        ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
          Set (projectiveSL n K)) ∧
      (IsSimpleGroup (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range ∧
        ¬ ∀ x y : (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range,
          x * y = y * x) ∧
      ((proj n K).comp (SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype)).ker =
        scalars n (semilinearFixedSubfield σ) ∧
      scalars n (semilinearFixedSubfield σ) =
        (scalars n K).comap (SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype) ∧
      Nat.card (scalars n K) = Nat.gcd n (ℓ ^ f - 1) ∧
      Nat.card (scalars n (semilinearFixedSubfield σ)) = Nat.gcd n (ℓ ^ (f / p) - 1) ∧
      fixingSubgroup (MulAut (projectiveSL n K))
          ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
            Set (projectiveSL n K)) = zpowers (fieldAut n K σ) ∧
      IsCyclic (zpowers (fieldAut n K σ)) ∧ Nat.card (zpowers (fieldAut n K σ)) = p := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hcard := card_semilinearFixedSubfield hℓ hf hK hσ
  have hpK : ¬ p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hpq
  refine ⟨hcard, linearSubfieldInclusion_injective (by omega) _,
    fixed_points_eq_range hk (by omega) (root_descent_of_not_dvd hp hk hσp hpK),
    simple_nonabelian_range_linearSubfieldInclusion hn _,
    ker_subfield_proj (by omega) _, scalars_eq_comap_map_subtype (by omega) _, ?_, ?_,
    fixingSubgroup_range_linearSubfieldInclusion hk hn, inferInstance, ?_⟩
  · rw [card_scalars (by omega), hK]
  · rw [card_scalars (by omega), hcard.2]
  · rw [Nat.card_zpowers, orderOf_fieldAut hn, hσ]

end CFSG.RankThree.PartOne
