module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.ZeroOrbitGeneratedFree

open MulAction

private theorem mem_join
    {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal] (x : G)
    (hx2 : x ^ 2 ∈ Q) {r : G} (hr : r ∈ Q ⊔ Subgroup.zpowers x) :
    r ∈ Q ∨ ∃ q : Q, r = q.val * x := by
  obtain ⟨q, hq, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hr
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hpow : x ^ n = (x ^ (2 : ℤ)) ^ (n / 2) * x ^ (n % 2) := by
    rw [← zpow_mul, ← zpow_add]
    congr 1
    omega
  have hQpow : (x ^ (2 : ℤ)) ^ (n / 2) ∈ Q :=
    Q.zpow_mem (by simpa only [zpow_ofNat] using hx2) _
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rw [hpow]
  rcases hn with hn | hn
  · exact Or.inl (by simpa only [hn, zpow_zero, mul_one] using Q.mul_mem hq hQpow)
  · refine Or.inr ⟨⟨q * (x ^ (2 : ℤ)) ^ (n / 2), Q.mul_mem hq hQpow⟩, ?_⟩
    simp only [hn, zpow_one, mul_assoc]

theorem generated_free
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) [Q.Normal] (x : G) (hx2 : x ^ 2 ∈ Q)
    (hQfree : ∀ (q : Q) (t : X), q • t = t → q = 1)
    (hzero : ∀ t : X, x • t ∉ orbit Q t) :
    ∀ (r : ↥(Q ⊔ Subgroup.zpowers x)) (t : X), r • t = t → r = 1 := by
  intro r t hrt
  rcases mem_join Q x hx2 r.property with hr | ⟨q, hr⟩
  · have hq : (⟨r.val, hr⟩ : Q) = 1 := hQfree ⟨r.val, hr⟩ t hrt
    exact Subtype.ext (congrArg (fun q : Q => q.val) hq)
  · apply False.elim
    apply hzero t
    apply mem_orbit_iff.mpr
    refine ⟨q⁻¹, ?_⟩
    change r.val • t = t at hrt
    rw [hr, mul_smul] at hrt
    exact (eq_inv_smul_iff.mpr hrt).symm

end FiveTransitive.ZeroOrbitGeneratedFree

end CFSG
