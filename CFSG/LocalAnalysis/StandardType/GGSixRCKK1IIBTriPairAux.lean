module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.RCKK1II

theorem rckTriP_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

theorem rckTriP_ker_conj {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 : MulAut.conj x y = y := by
      have h2 := congrArg (fun f : MulAut G => f y) h
      simpa using h2
    rw [MulAut.conj_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  · intro h
    ext y
    have h1 : MulAut.conj x y = y := by
      rw [MulAut.conj_apply, ← h y]
      group
    simpa using h1

theorem rckTriP_zpowers_eq_of_involution {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : y = x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxord : orderOf x = 2 := rckTriP_orderOf_eq_two hx1 hx2
  have h1 : x ^ (k % 2) = x ^ k := by
    have h := zpow_mod_orderOf x k
    rw [hxord] at h
    exact h
  rw [← h1] at hk
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hk
    exact absurd hk.symm hy1
  · rw [h, zpow_one] at hk
    exact hk.symm

end CFSG.StandardType.RCKK1II
