module

public import CFSG.Quasithin.EmptyFaithful.S14612GA2

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

theorem conjBy_eq_of_involution (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X)
    (hx2 : orderOf x = 2) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) : conjBy x Q = Q := by
  have key : ∀ q ∈ Q, x * q * x⁻¹ = q⁻¹ := fun q hq => h.inverts_of_involution hx hx2 q (hQ hq)
  ext y
  constructor
  · intro hy
    have hq := mem_conjBy_iff.mp hy
    have h1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [key _ hq] at h1
    rw [← h1]
    exact Q.inv_mem hq
  · intro hy
    have h1 := mem_conjBy_of_mem (g := x) (Q.inv_mem hy)
    rwa [key y⁻¹ (Q.inv_mem hy), inv_inv] at h1

theorem zmod_three_mul_self_add_one_ne_zero (m : ZMod 3) : m * m + 1 ≠ 0 := by
  revert m
  decide

theorem conjBy_ne_of_orderOf_four (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X)
    (hx4 : orderOf x = 4) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3) :
    conjBy x Q ≠ Q := by
  intro hconj
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqQ, -, hgz, hq3⟩ := exists_generator_of_prime_card hQ3
  have hu2 : orderOf (x ^ 2) = 2 := by rw [orderOf_pow' _ (by norm_num), hx4]; norm_num
  have hinv : x ^ 2 * q * (x ^ 2)⁻¹ = q⁻¹ :=
    h.inverts_of_involution (X.pow_mem hx 2) hu2 q (hQ hqQ)
  have hmem : x * q * x⁻¹ ∈ Subgroup.zpowers q := by
    rw [hgz, ← hconj]
    exact mem_conjBy_of_mem hqQ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h2 : x ^ 2 * q * (x ^ 2)⁻¹ = q ^ (n * n) := by
    calc x ^ 2 * q * (x ^ 2)⁻¹ = x * (x * q * x⁻¹) * x⁻¹ := by rw [pow_two]; group
      _ = x * q ^ n * x⁻¹ := by rw [← hn]
      _ = (x * q * x⁻¹) ^ n := conj_zpow.symm
      _ = q ^ (n * n) := by rw [← hn, ← zpow_mul]
  rw [hinv] at h2
  have h3 : q ^ (n * n + 1) = 1 := by rw [zpow_add_one, ← h2]; simp
  have h4 : ((3 : ℕ) : ℤ) ∣ n * n + 1 := by
    rw [← hq3]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd (n * n + 1) 3).mpr h4
  push_cast at h5
  exact zmod_three_mul_self_add_one_ne_zero _ h5

end E9Z4Str

end CFSG.Quasithin
