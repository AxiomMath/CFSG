module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

theorem exists_inv_of_central_two_kernel {L S : Type*} [Group L] [Finite L] [Group S]
    (π : L →* S) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center L)
    (h2 : IsPGroup 2 π.ker) (γ : MulAut L) (γbar : S →* S) (hcompat : ∀ x, π (γ x) = γbar (π x))
    {y : S} (hy : γbar y = y⁻¹) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : orderOf y = r) :
    ∃ x : L, γ x = x⁻¹ ∧ orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, rfl⟩ := hπ y
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h2
  have hker : x₀ ^ r ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hyr, pow_orderOf_eq_one]
  have hxr : (x₀ ^ Nat.card π.ker) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x₀ ^ r, hker⟩ : π.ker)))
  have hyk : π x₀ ^ Nat.card π.ker ≠ 1 := by
    intro h1
    have h := orderOf_dvd_of_pow_eq_one h1
    rw [hyr, hj] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  set x := x₀ ^ Nat.card π.ker with hxdef
  have hx1 : x ≠ 1 := fun h => hyk (by rw [← map_pow, ← hxdef, h, map_one])
  refine ⟨x, ?_, orderOf_eq_prime hxr hx1⟩
  set q := γ x * x with hqdef
  have hπγx : π (γ x) = (π x)⁻¹ := by
    rw [hcompat, hxdef, map_pow, map_pow, hy, inv_pow]
  have hq : q ∈ π.ker := by
    rw [MonoidHom.mem_ker, hqdef, map_mul, hπγx, inv_mul_cancel]
  have hγx : γ x = q * x⁻¹ := by rw [hqdef, mul_assoc, mul_inv_cancel, mul_one]
  have hqr : q ^ r = 1 := by
    have h1 : (γ x) ^ r = 1 := by rw [← map_pow, hxr, map_one]
    have hcomm : Commute q x := (Subgroup.mem_center_iff.1 (hc hq) x).symm
    have hcomm' : Commute q x⁻¹ := hcomm.inv_right
    rw [hγx, hcomm'.mul_pow, inv_pow, hxr, inv_one, mul_one] at h1
    exact h1
  have hq1 : q = 1 := by
    obtain ⟨i, hi⟩ := h2 ⟨q, hq⟩
    have hd1 : orderOf q ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hi)
    have hd2 : orderOf q ∣ r := orderOf_dvd_of_pow_eq_one hqr
    have hcop : Nat.Coprime (2 ^ i) r :=
      Nat.Coprime.pow_left i ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [hγx, hq1, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
