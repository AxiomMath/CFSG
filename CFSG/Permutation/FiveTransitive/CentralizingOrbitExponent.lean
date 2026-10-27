module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.CentralizingOrbitExponent
open MulAction

theorem pow_smul_eq
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (p : ℕ) (hQ : ∀ q : Q, q ^ p = 1)
    (g : G) (hc : ∀ q : Q, Commute g q.val) (x : X)
    (hx : ∃ q : Q, g • x = q • x) : (g ^ p) • x = x := by
  obtain ⟨q,hq⟩ := hx
  have hmem : q.val⁻¹ * g ∈ stabilizer G x := by
    change (q.val⁻¹ * g) • x = x
    rw [mul_smul, hq]
    exact inv_smul_smul q.val x
  have hpow := (stabilizer G x).pow_mem hmem p
  have hqp : q.val ^ p = 1 := congrArg Subtype.val (hQ q)
  rw [(hc q).symm.inv_left.mul_pow, inv_pow, hqp, inv_one, one_mul] at hpow
  exact hpow

theorem smul_eq_of_square_eq_one
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (hQ : ∀ q : Q, q ^ 5 = 1)
    (g : G) (hc : ∀ q : Q, Commute g q.val) (hg : g ^ 2 = 1)
    (x : X) (hx : ∃ q : Q, g • x = q • x) : g • x = x := by
  have hp := pow_smul_eq Q 5 hQ g hc x hx
  have hg5 : g ^ 5 = g := by
    calc
      g ^ 5 = (g ^ 2) ^ 2 * g := by rw [← pow_mul]; exact pow_succ g 4
      _ = g := by rw [hg, one_pow, one_mul]
  rwa [hg5] at hp

end FiveTransitive.CentralizingOrbitExponent

end CFSG
