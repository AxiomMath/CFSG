module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.CoprimeCentralizerOrbit

open MulAction

theorem fixed_of_commute
    {G X : Type*} [Group G] [MulAction G X]
    (z r : G) (hcomm : Commute z r) (hcop : (orderOf r).Coprime (orderOf z))
    (x : X) (h : z • x = r • x) : z • x = x := by
  have hp : ∀ k : ℕ, z ^ k • x = r ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        z ^ (k + 1) • x = z • (z ^ k • x) := by rw [pow_succ',mul_smul]
        _ = z • (r ^ k • x) := by rw [ih]
        _ = r ^ k • (z • x) := by rw [←mul_smul,(hcomm.pow_right k).eq,mul_smul]
        _ = r ^ (k + 1) • x := by rw [h,pow_succ,mul_smul]
  have hpow : z ^ orderOf r ∈ stabilizer G x := by
    change z ^ orderOf r • x = x
    rw [hp,pow_orderOf_eq_one,one_smul]
  have hz : z ∈ Subgroup.zpowers (z ^ orderOf r) := mem_zpowers_pow_iff.mpr hcop
  exact (Subgroup.zpowers_le.mpr hpow) hz

theorem fixed_of_mem_orbit
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (z : G)
    (hcentral : z ∈ Subgroup.centralizer (Q : Set G))
    (hcop : ∀ r : Q, (orderOf r).Coprime (orderOf z))
    (x : X) (horbit : z • x ∈ orbit Q x) : z • x = x := by
  obtain ⟨r,hr⟩ := mem_orbit_iff.mp horbit
  have hc : Commute z (r : G) := by
    exact (Subgroup.mem_centralizer_iff.mp hcentral r r.property).symm
  apply fixed_of_commute z (r : G) hc
  · simpa only [Subgroup.orderOf_coe] using hcop r
  · exact hr.symm

end FiveTransitive.CoprimeCentralizerOrbit

end CFSG
