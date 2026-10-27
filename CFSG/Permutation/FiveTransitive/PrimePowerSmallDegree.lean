module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.PrimePowerSmallDegree

theorem pow_eq_one
    {X : Type*} [Fintype X] [DecidableEq X]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card X < p ^ 2)
    (g : Equiv.Perm X) (he : ∃ e : ℕ, orderOf g = p ^ e) : g ^ p = 1 := by
  obtain ⟨e,he⟩ := he
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← g.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro d hd
  have hdd := Equiv.Perm.dvd_of_mem_cycleType hd
  rw [he] at hdd
  obtain ⟨k,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp hdd
  have hkbound : p ^ k < p ^ 2 :=
    ((Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hd).trans g.sum_cycleType_le).trans_lt hcard
  have hk : k ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ k)
    omega
  simpa only [pow_one] using pow_dvd_pow p hk

end FiveTransitive.PrimePowerSmallDegree

end CFSG
