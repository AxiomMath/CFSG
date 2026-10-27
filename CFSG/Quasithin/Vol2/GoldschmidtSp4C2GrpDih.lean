module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpCoord
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpOpp

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt antiUnipotent)

theorem exists_conj_of_inter_trivial {G : Type*} [Group G] [Finite G] {z r : G} (hz : z * z = 1)
    (hr : r * r = 1) (h : ∀ t : G, t * z = z * t → t * r = r * t → t = 1) :
    ∃ y ∈ Subgroup.closure ({z, r} : Set G), y * z * y⁻¹ = r := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  set p := z * r with hp
  have hpinv : p⁻¹ = r * z := by rw [hp, mul_inv_rev, hr', hz']
  have hzp : z * p * z⁻¹ = p⁻¹ := by
    rw [hz', hpinv, hp]
    calc z * (z * r) * z = (z * z) * r * z := by group
      _ = r * z := by rw [hz, one_mul]
  have hrp : r * p * r⁻¹ = p⁻¹ := by
    rw [hr', hpinv, hp]
    calc r * (z * r) * r = r * z * (r * r) := by group
      _ = r * z := by rw [hr, mul_one]
  have hzpow : ∀ n : ℕ, z * p ^ n * z = (p ^ n)⁻¹ := fun n => by
    calc z * p ^ n * z = z * p ^ n * z⁻¹ := by rw [hz']
      _ = (z * p * z⁻¹) ^ n := conj_pow.symm
      _ = (p ^ n)⁻¹ := by rw [hzp, inv_pow]
  have hrpow : ∀ n : ℕ, r * p ^ n * r = (p ^ n)⁻¹ := fun n => by
    calc r * p ^ n * r = r * p ^ n * r⁻¹ := by rw [hr']
      _ = (r * p * r⁻¹) ^ n := conj_pow.symm
      _ = (p ^ n)⁻¹ := by rw [hrp, inv_pow]
  have hodd : Odd (orderOf p) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    obtain ⟨m, hm⟩ := hne
    have hpos : 0 < orderOf p := orderOf_pos p
    have hm0 : 0 < m := by omega
    have ht2 : p ^ m * p ^ m = 1 := by
      rw [← pow_add, ← hm]
      exact pow_orderOf_eq_one p
    have ht1 : p ^ m ≠ 1 := by
      intro h1
      have := orderOf_le_of_pow_eq_one hm0 h1
      omega
    have hti : (p ^ m)⁻¹ = p ^ m := inv_eq_of_mul_eq_one_right ht2
    have hzt : p ^ m * z = z * p ^ m := by
      have h1 := hzpow m
      rw [hti] at h1
      calc p ^ m * z = (z * p ^ m * z) * z := by rw [h1]
        _ = z * p ^ m := by rw [mul_assoc, hz, mul_one]
    have hrt : p ^ m * r = r * p ^ m := by
      have h1 := hrpow m
      rw [hti] at h1
      calc p ^ m * r = (r * p ^ m * r) * r := by rw [h1]
        _ = r * p ^ m := by rw [mul_assoc, hr, mul_one]
    exact ht1 (h _ hzt hrt)
  obtain ⟨j, hj⟩ := hodd
  have hpow1 : p ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one p
  have hp2j : p ^ (2 * j) = p⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hpow1)
  refine ⟨p ^ j, Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) j, ?_⟩
  calc p ^ j * z * (p ^ j)⁻¹ = p ^ j * z * (z * p ^ j * z) := by rw [hzpow j]
    _ = p ^ (2 * j) * z := by
        calc p ^ j * z * (z * p ^ j * z) = p ^ j * (z * z) * p ^ j * z := by group
          _ = p ^ (2 * j) * z := by rw [hz, mul_one, ← pow_add, two_mul]
    _ = r := by rw [hp2j, hpinv, mul_assoc, hz, mul_one]

variable {k : Type} [Field k] [CharP k 2]

theorem exists_conj_ref [Finite k] {b c b₁ c₁ : k} (hb : b ≠ 0) (hc : c ≠ 0) (hb₁ : b₁ ≠ 0)
    (hc₁ : c₁ ≠ 0) {g : antiSp k} (hg : IsOppStd g) :
    ∃ y ∈ Subgroup.closure ({uElt 0 b c 0, g * uElt 0 b₁ c₁ 0 * g⁻¹} : Set (antiSp k)),
      y * uElt 0 b c 0 * y⁻¹ = g * uElt 0 b₁ c₁ 0 * g⁻¹ := by
  refine exists_conj_of_inter_trivial (P6B.uElt_center_mul_self b c) ?_ ?_
  · calc g * uElt 0 b₁ c₁ 0 * g⁻¹ * (g * uElt 0 b₁ c₁ 0 * g⁻¹)
        = g * (uElt 0 b₁ c₁ 0 * uElt 0 b₁ c₁ 0) * g⁻¹ := by group
      _ = 1 := by rw [P6B.uElt_center_mul_self]; group
  · intro t htz htr
    have ht : t ∈ antiUnipotent k := mem_unipotent_of_comm hb hc htz
    have ht' : g⁻¹ * t * g ∈ antiUnipotent k := by
      apply mem_unipotent_of_comm hb₁ hc₁
      calc g⁻¹ * t * g * uElt 0 b₁ c₁ 0
          = g⁻¹ * (t * (g * uElt 0 b₁ c₁ 0 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * uElt 0 b₁ c₁ 0 * g⁻¹) * t) * g := by rw [htr]
        _ = uElt 0 b₁ c₁ 0 * (g⁻¹ * t * g) := by group
    exact eq_one_of_conj_mem hg ht ht'

end CFSG.Quasithin.Ch3E213M.Sp4C2
