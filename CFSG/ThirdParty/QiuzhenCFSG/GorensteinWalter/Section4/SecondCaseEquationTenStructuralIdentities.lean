module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The index-tower identity used by Section 4 equation (10)

If `X` is contained in two finite subgroups `H` and `M`, the two relative-index
towers from `X` to the ambient group have the same bottom index.  This is the
group-theoretic part of the equation-(10) factorization; the rational parameter
conversion is deliberately left to the downstream arithmetic endpoint.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Equality of the two index towers through a common subgroup `X`.

The statement is intentionally independent of any Section-4 names: later
constructors may instantiate `X` with `H ∩ M` and identify the two relative
indices with `u * p₀` and `q * k'`.
-/
public theorem secondCase_index_tower_eq
    {G : Type u} [Group G] [Finite G]
    (H M X : Subgroup G)
    (hXH : X ≤ H) (hXM : X ≤ M) :
    X.relIndex H * H.index = X.relIndex M * M.index := by
  have hH := Subgroup.relIndex_mul_index hXH
  have hM := Subgroup.relIndex_mul_index hXM
  omega

/-- Rational form of the index-tower identity after naming the two relative
indices.  This is the exact factorization required by equation (10).
-/
public theorem secondCase_index_tower_factor
    {G : Type u} [Group G] [Finite G]
    (H M X : Subgroup G)
    (hXH : X ≤ H) (hXM : X ≤ M)
    {a b : ℕ}
    (ha : X.relIndex H = a) (hb : X.relIndex M = b) :
    (H.index : ℚ) * (a : ℚ) = (b : ℚ) * (M.index : ℚ) := by
  have h := secondCase_index_tower_eq H M X hXH hXM
  rw [ha, hb] at h
  have h' : H.index * a = b * M.index := by
    simpa [Nat.mul_comm] using h
  exact_mod_cast h'

/-- Direct equation-(10) shape of the tower identity.  The hypotheses
identify the two relative indices and the ambient `M`-index with the rational
parameters used by `secondCase_equation10_of_theorem_A`. -/
public theorem secondCase_index_tower_factor_eq10
    {G : Type u} [Group G] [Finite G]
    (H M X : Subgroup G)
    (hXH : X ≤ H) (hXM : X ≤ M)
    {a b : ℕ} (ha : X.relIndex H = a) (hb : X.relIndex M = b)
    {q k' u p0 m : ℚ}
    (ha' : (a : ℚ) = u * p0)
    (hb' : (b : ℚ) = q * k')
    (hm : m = (M.index : ℚ)) :
    (H.index : ℚ) * (u * p0) = q * k' * m := by
  have ht := secondCase_index_tower_factor H M X hXH hXM ha hb
  calc
    (H.index : ℚ) * (u * p0) = (H.index : ℚ) * (a : ℚ) := by rw [ha']
    _ = (b : ℚ) * (M.index : ℚ) := ht
    _ = q * k' * m := by rw [hb', hm]

/-- Convenience specialization for the actual intersection `H ⊓ M`. -/
public theorem secondCase_inf_index_tower_factor_eq10
    {G : Type u} [Group G] [Finite G]
    (H M : Subgroup G)
    {a b : ℕ} (ha : (H ⊓ M).relIndex H = a)
    (hb : (H ⊓ M).relIndex M = b)
    {q k' u p0 m : ℚ}
    (ha' : (a : ℚ) = u * p0)
    (hb' : (b : ℚ) = q * k')
    (hm : m = (M.index : ℚ)) :
    (H.index : ℚ) * (u * p0) = q * k' * m := by
  exact secondCase_index_tower_factor_eq10 H M (H ⊓ M)
    inf_le_left inf_le_right ha hb ha' hb' hm

end CFSG.GorensteinWalter
