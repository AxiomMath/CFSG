module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

namespace CFSG
end CFSG
open CFSG

namespace CFSG.PGroup

open scoped Pointwise

section OmegaFrattini

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)]


section Action

variable {A : Type*} [Group A] [MulDistribMulAction A G]


/-- If `A` fixes every element of order `p`, then it acts trivially on `Ω₁(G)`. -/
public theorem actsTriviallyOnSubgroup_omega₁_of_fix_order_p
    (hfixp : ∀ x : G, orderOf x = p → ∀ a : A, a • x = x) :
    ActsTriviallyOnSubgroup (A := A) (G := G) (omega₁ (G := G) (p := p)) := by
  let _ := (inferInstance : Finite G)
  let _ := (inferInstance : Fact (IsPGroup p G))
  have hgen_fix : {x : G | x ^ (p ^ 1) = 1} ⊆ fixedPointSubgroup A G := by
    intro x hx
    have hxpow : x ^ p = 1 := by simpa [pow_one] using hx
    by_cases hx1 : x = 1
    · simp [hx1, fixedPointSubgroup]
    · have hx_order_dvd_p : orderOf x ∣ p := (orderOf_dvd_iff_pow_eq_one).2 hxpow
      have hx_order_eq_p : orderOf x = p := by
        rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hx_order_dvd_p with h1 | hp
        · exfalso
          exact hx1 (orderOf_eq_one_iff.mp h1)
        · exact hp
      exact (FixedPoints.mem_subgroup (M := A) (a := x)).2 (hfixp x hx_order_eq_p)
  have hΩ_le_fixed : omega₁ (G := G) (p := p) ≤ fixedPointSubgroup A G := by
    rw [omega₁, omega]
    exact (Subgroup.closure_le (K := fixedPointSubgroup A G)).2 hgen_fix
  intro a x hx
  have hxfix : x ∈ fixedPointSubgroup A G := hΩ_le_fixed hx
  exact (FixedPoints.mem_subgroup (M := A) (a := x)).1 hxfix a

end Action


end OmegaFrattini

end CFSG.PGroup
