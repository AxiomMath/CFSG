module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin

variable {G : Type} [Group G]

theorem commutator_normalized {K : Subgroup G} {a : G} (ha : a ∈ K) {z : G} (hz : z ∈ ⁅K, K⁆) :
    a * z * a⁻¹ ∈ ⁅K, K⁆ := by
  have hK : K.map (MulAut.conj a).toMonoidHom = K := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact K.mul_mem (K.mul_mem ha hv) (K.inv_mem ha)
    · intro hw
      refine ⟨a⁻¹ * w * a, K.mul_mem (K.mul_mem (K.inv_mem ha) hw) ha, ?_⟩
      show a * (a⁻¹ * w * a) * a⁻¹ = w
      group
  have h := Subgroup.map_commutator K K (MulAut.conj a).toMonoidHom
  rw [hK] at h
  have : a * z * a⁻¹ ∈ Subgroup.map (MulAut.conj a).toMonoidHom ⁅K, K⁆ := ⟨z, hz, rfl⟩
  rwa [h] at this

theorem pow_mul_commutator {K : Subgroup G} {c o : G} (hc : c ∈ ⁅K, K⁆) (ho : o ∈ K) (m : ℕ) :
    ∃ z ∈ ⁅K, K⁆, (c⁻¹ * o) ^ m = z * o ^ m := by
  induction m with
  | zero => exact ⟨1, (⁅K, K⁆).one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨z, hz, hm⟩ := ih
    refine ⟨z * (o ^ m * c⁻¹ * (o ^ m)⁻¹), (⁅K, K⁆).mul_mem hz
      (commutator_normalized (K.pow_mem ho m) ((⁅K, K⁆).inv_mem hc)), ?_⟩
    rw [pow_succ, hm, pow_succ]
    group

theorem mem_commutator_of_inverting {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hodd : Odd (orderOf x)) {k : ℕ} (hk : (y * x * y⁻¹ * x) ^ 2 ^ k = 1) : x ∈ ⁅K, K⁆ := by
  have hc : y * x * y⁻¹ * x⁻¹ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator hy hx
  have ho : y * x * y⁻¹ * x ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hy hx) (K.inv_mem hy)) hx
  have hx2 : x ^ 2 = (y * x * y⁻¹ * x⁻¹)⁻¹ * (y * x * y⁻¹ * x) := by
    rw [pow_two]
    group
  obtain ⟨z, hz, hzo⟩ := pow_mul_commutator hc ho (2 ^ k)
  rw [← hx2, hk, mul_one] at hzo
  have hxz : x ^ 2 ^ (k + 1) ∈ ⁅K, K⁆ := by
    have : x ^ 2 ^ (k + 1) = (x ^ 2) ^ 2 ^ k := by
      rw [← pow_mul, ← pow_succ']
    rw [this, hzo]
    exact hz
  have hcop : Nat.Coprime (2 ^ (k + 1)) (orderOf x) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨j, hj⟩ := hodd
    omega
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  exact (Subgroup.zpowers_le.2 hxz) hmem

end CFSG.Quasithin.FLc
