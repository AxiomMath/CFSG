module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

theorem commV_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem conj_transv_apply {a g : MulAut V} {v₁ : V}
    (hc : commV (Subgroup.zpowers a) = Subgroup.zpowers v₁) (hv₁ : v₁ ^ 2 = 1) (w : V) :
    (g⁻¹ * a * g) w = w ∨ (g⁻¹ * a * g) w = g⁻¹ v₁ * w := by
  rcases apply_eq_or_of_commV hc hv₁ (g w) with h | h
  · left
    simp only [MulAut.mul_apply, h, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · right
    simp only [MulAut.mul_apply, h, map_mul, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem mem_commV_conj {a g : MulAut V} {v₁ : V}
    (hc : commV (Subgroup.zpowers a) = Subgroup.zpowers v₁) (hv₁ : v₁ ^ 2 = 1) (ha : a ≠ 1) :
    g⁻¹ v₁ ∈ commV (Subgroup.zpowers (g⁻¹ * a * g)) := by
  obtain ⟨w, hw⟩ : ∃ w, a w ≠ w := by
    by_contra hall
    push Not at hall
    exact ha (MulEquiv.ext hall)
  have h := (apply_eq_or_of_commV hc hv₁ w).resolve_left hw
  refine Subgroup.subset_closure ⟨g⁻¹ * a * g, Subgroup.mem_zpowers _, g⁻¹ w, ?_⟩
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply, h, map_mul,
    mul_inv_cancel_right]

variable {M : Type*} [Group M]

theorem sq_mem_of_mem_sup_zpowers {K : Subgroup M} {t : M} (ht : t ^ 2 = 1)
    (htK : t ∈ Subgroup.normalizer (K : Set M)) {z : M} (hz : z ∈ K ⊔ Subgroup.zpowers t) :
    z ^ 2 ∈ K := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set M) := Subgroup.zpowers_le.mpr htK
  have hz' : z ∈ ((Subgroup.zpowers t ⊔ K : Subgroup M) : Set M) := by
    rw [sup_comm]
    exact hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hz'
  obtain ⟨x, hx, k, hk, rfl⟩ := hz'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hconj : t ^ i * k * (t ^ i)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hle (Subgroup.zpow_mem_zpowers t i)) k).mp hk
  have ht2i : t ^ i * t ^ i = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_ofNat, ht, one_zpow]
  have e : (t ^ i * k) ^ 2 = (t ^ i * k * (t ^ i)⁻¹) * (t ^ i * t ^ i) * k := by
    rw [pow_two]
    group
  rw [e, ht2i, mul_one]
  exact K.mul_mem hconj hk

theorem mem_of_odd_of_mem_sup_zpowers [Finite M] {K : Subgroup M} {t : M} (ht : t ^ 2 = 1)
    (htK : t ∈ Subgroup.normalizer (K : Set M)) {z : M} (hz : z ∈ K ⊔ Subgroup.zpowers t)
    (hodd : Odd (orderOf z)) : z ∈ K := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : z = (z ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact K.pow_mem (sq_mem_of_mem_sup_zpowers ht htK hz) _

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
