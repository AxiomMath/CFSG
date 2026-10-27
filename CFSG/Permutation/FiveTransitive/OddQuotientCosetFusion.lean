module

public import CFSG.Permutation.FiveTransitive.OddKernelEqualImageConjugacy

public section

namespace CFSG

namespace FiveTransitive.OddQuotientCosetFusion

theorem exists_ker_conjugator_mod_subgroup
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : f a = f b) (hfb : f b ≠ 1) :
    ∃ k : G, k ∈ f.ker ∧ (k * a * k⁻¹) * b⁻¹ ∈ Q := by
  let pi : G →* G ⧸ Q := QuotientGroup.mk' Q
  let rho : G ⧸ Q →* A := QuotientGroup.lift Q f hQ
  have hrho (x : G) : rho (pi x) = f x := rfl
  have hodd' : Odd (Nat.card rho.ker) := by
    simpa only [rho, QuotientGroup.ker_lift] using hodd
  obtain ⟨kbar, hkbar, heq⟩ := OddKernelEqualImageConjugacy.exists_ker_conjugator rho hodd'
    (pi a) (pi b) (by rw [← map_pow, ha, map_one])
    (by rw [← map_pow, hb, map_one]) hab hfb
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective Q kbar
  refine ⟨k, hkbar, ?_⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change pi ((k * a * k⁻¹) * b⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, heq, mul_inv_cancel]

end FiveTransitive.OddQuotientCosetFusion

end CFSG
