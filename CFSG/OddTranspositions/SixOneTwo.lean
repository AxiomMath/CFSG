module

public import CFSG.OddTranspositions.PartTwoSec6
public import CFSG.Timmesfeld.Bridge.Asc72Minimal

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_normal_of_mem_closure_commSet {D : Set G} (hodd : Asc72.IsOddTransp D)
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N)) {u : G} (hu : u ∈ D)
    (huD : u ∈ Subgroup.closure (commSet D u))
    (huxD : ∀ x ∈ N, x ≠ 1 → u * x * u = x⁻¹ → u * x ∈ D) :
    ∀ x ∈ N, Commute u x := by
  intro x hxN
  by_contra hcomm
  have hu2 : u * u = 1 := hodd.mul_self_eq_one hu
  have huxu_ne : u * x * u ≠ x := by
    intro h
    apply hcomm
    have h' : u * x = x * u := by
      have := congrArg (fun z => z * u) h
      simpa [mul_assoc, hu2] using this
    exact h'
  set y : G := x⁻¹ * (u * x * u) with hy
  have huxuN : u * x * u ∈ N := by
    simpa [hodd.inv_eq hu] using hN.conj_mem x hxN u
  have hyN : y ∈ N := N.mul_mem (N.inv_mem hxN) huxuN
  have hy_ne : y ≠ 1 := by
    intro h
    apply huxu_ne
    have := congrArg (fun z => x * z) h
    simpa [hy, mul_assoc] using this
  have hyinv : u * y * u = y⁻¹ := by
    rw [hy]
    simp [mul_assoc, hu2, hodd.inv_eq hu]
  set w : G := u * y with hw
  have hwD : w ∈ D := huxD y hyN hy_ne hyinv
  have hwu : w = y⁻¹ * u := by
    rw [hw]
    have := congrArg (fun z => z * u) hyinv
    simpa [hw, mul_assoc, hu2] using this
  have hwW : w ∈ Wmem D u :=
    mem_Wmem_of_mem_mul_normal hodd hN hNo hu hwD (N.inv_mem hyN) hwu
  have hu_closure : u ∈ Subgroup.closure (commSet D w) := by
    rw [(mem_Wmem.mp hwW).2]
    exact huD
  have hle : Subgroup.closure (commSet D w) ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      obtain ⟨-, hzw, -⟩ := hz
      exact hzw)
  have hcomm_uw : Commute u w :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hu_closure)
  have hy_eq_inv : y = y⁻¹ := by
    have h1 : u * w = w * u := hcomm_uw
    have hleft : u * w = y := by
      rw [hw, ← mul_assoc, hu2, one_mul]
    rw [hleft, hyinv] at h1
    exact h1
  have hy2 : y * y = 1 := mul_eq_one_iff_eq_inv.mpr hy_eq_inv
  have hodd_y : Odd (orderOf y) :=
    hNo.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hyN)
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hy2)
  have hord : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd h (hodd_y.ne_two_of_dvd_nat (dvd_refl (orderOf y)))
  exact hy_ne (orderOf_eq_one_iff.mp hord)

theorem normal_le_center_of_mem_closure_commSet {D : Set G} (hS : Asc72.Setup G D)
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N)) {u : G} (hu : u ∈ D)
    (huD : u ∈ Subgroup.closure (commSet D u))
    (huxD : ∀ x ∈ N, x ≠ 1 → u * x * u = x⁻¹ → u * x ∈ D) :
    N ≤ Subgroup.center G := by
  haveI : N.Normal := hN
  refine Setup.le_center_of_mem_centralizer (D := D) (N := N) hS hu ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hcomm := commute_of_mem_normal_of_mem_closure_commSet hS.oddT hN hNo hu huD huxD x hx
  exact hcomm.eq.symm

end CFSG.OddTranspositions
