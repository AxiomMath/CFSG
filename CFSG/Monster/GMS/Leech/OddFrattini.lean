module

public import CFSG.Monster.GMS.Leech.OddLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

private theorem orderOf_conj_aux {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (show g * x = g * x * g⁻¹ * g by group)).symm

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem exists_conj_of_odd_pair
    [Finite G] (hI : Co1InvolutionFacts) {t y y' g : G}
    (h : IsLeechCentralLift z t) (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hy' : y' ∈ Subgroup.centralizer ({z} : Set G)) (hy2 : y * y = 1) (hy'2 : y' * y' = 1)
    (hodd : Odd (orderOf (t * y))) (hodd' : Odd (orderOf (t * y')))
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (hgt : t⁻¹ * (g * t * g⁻¹) ∈ leechQ z)
    (hgy : y'⁻¹ * (g * y * g⁻¹) ∈ leechQ z) :
    ∃ p ∈ leechQ z, p * g ∈ Subgroup.centralizer ({t} : Set G) ∧
      p * g * y * (p * g)⁻¹ = y' := by
  have hMn : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ leechQ z, g * q * g⁻¹ ∈ leechQ z :=
    fun g hg q hq => L.conj_mem' hg hq
  have hMw : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have ht2 : t * t = 1 := h.mul_self
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨p₁, hp₁, hp₁g⟩ := L.exists_mul_mem_centralizer_of_lift hI h hg hgt
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = p₁ * g := ⟨_, rfl⟩
  rw [← hg₁] at hp₁g
  have hg₁C : g₁ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [hg₁]; exact mul_mem (L.mem_centralizer hp₁) hg
  have hg₁t : g₁ * t * g₁⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hp₁g
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  obtain ⟨y₁, hy₁def⟩ : ∃ y₁, y₁ = g₁ * y * g₁⁻¹ := ⟨_, rfl⟩
  have hy₁C : y₁ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [hy₁def]; exact mul_mem (mul_mem hg₁C hy) (inv_mem hg₁C)
  have hy₁2 : y₁ * y₁ = 1 := by
    rw [hy₁def]
    calc g₁ * y * g₁⁻¹ * (g₁ * y * g₁⁻¹) = g₁ * (y * y) * g₁⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hy₁i : y₁⁻¹ = y₁ := inv_eq_of_mul_eq_one_right hy₁2
  have hy'i : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'2
  have hy₁y' : y₁⁻¹ * y' ∈ leechQ z := by
    have hw : (g * y * g⁻¹)⁻¹ * y' ∈ leechQ z := by
      have := inv_mem hgy
      rwa [mul_inv_rev, inv_inv] at this
    have hc1 : p₁ * ((g * y * g⁻¹)⁻¹ * y') * p₁⁻¹ ∈ leechQ z :=
      mul_mem (mul_mem hp₁ hw) (inv_mem hp₁)
    have hc2 : p₁ * (y'⁻¹ * p₁⁻¹ * y') ∈ leechQ z := by
      have := hMn y'⁻¹ (inv_mem hy') p₁⁻¹ (inv_mem hp₁)
      rw [inv_inv] at this
      exact mul_mem hp₁ this
    have : y₁⁻¹ * y' = (p₁ * ((g * y * g⁻¹)⁻¹ * y') * p₁⁻¹) * (p₁ * (y'⁻¹ * p₁⁻¹ * y')) := by
      rw [hy₁def, hg₁]; group
    rw [this]
    exact mul_mem hc1 hc2
  have hd : t * y₁ = g₁ * (t * y) * g₁⁻¹ := by
    calc t * y₁ = (g₁ * t * g₁⁻¹) * (g₁ * y * g₁⁻¹) := by rw [hg₁t, hy₁def]
      _ = g₁ * (t * y) * g₁⁻¹ := by group
  have hm : Odd (orderOf (t * y₁)) := by
    rw [hd, orderOf_conj_aux]
    exact hodd
  have hdC : t * y₁ ∈ Subgroup.centralizer ({z} : Set G) := mul_mem h.mem_centralizer hy₁C
  have huC : t * y' ∈ Subgroup.centralizer ({z} : Set G) := mul_mem h.mem_centralizer hy'
  have hdu : (t * y₁)⁻¹ * (t * y') ∈ leechQ z := by
    rw [show (t * y₁)⁻¹ * (t * y') = y₁⁻¹ * y' by group]
    exact hy₁y'
  have hum : (t * y') ^ orderOf (t * y₁) = 1 := by
    have h1 := inv_pow_mul_pow_mem_of_conj_mem hMn hdC hdu (orderOf (t * y₁))
    rw [pow_orderOf_eq_one, inv_one, one_mul] at h1
    exact L.eq_one_of_odd_orderOf h1 (hodd'.of_dvd_nat (orderOf_pow_dvd _))
  have hxd : t * (t * y₁) * t = (t * y₁)⁻¹ := by
    calc t * (t * y₁) * t = (t * t) * y₁ * t := by group
      _ = (t * y₁)⁻¹ := by rw [ht2, one_mul, mul_inv_rev, hti, hy₁i]
  have hxu : t * (t * y') * t = (t * y')⁻¹ := by
    calc t * (t * y') * t = (t * t) * y' * t := by group
      _ = (t * y')⁻¹ := by rw [ht2, one_mul, mul_inv_rev, hti, hy'i]
  obtain ⟨q, hq, hqd, hqx⟩ := L.extraspecial.exists_conj_of_inverting hMn hMw h.mem_centralizer
    hdC huC hm (pow_orderOf_eq_one _) hum ht2 hxd hxu hdu
  have hqt : q * t * q⁻¹ = t := by
    rcases hqx with h1 | h1
    · exact h1
    · exact absurd h1 (h.ne_conj (L.mem_centralizer hq))
  have hqy : q * y₁ * q⁻¹ = y' := by
    have h1 : t * (q * y₁ * q⁻¹) = t * y' := by
      calc t * (q * y₁ * q⁻¹) = (q * t * q⁻¹) * (q * y₁ * q⁻¹) := by rw [hqt]
        _ = q * (t * y₁) * q⁻¹ := by group
        _ = t * y' := hqd
    exact mul_left_cancel h1
  refine ⟨q * p₁, mul_mem hq hp₁, ?_, ?_⟩
  · rw [show q * p₁ * g = q * g₁ by rw [hg₁, mul_assoc]]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 : g₁ * t = t * g₁ := Subgroup.mem_centralizer_singleton_iff.mp hp₁g
    have h2 : q * t = t * q := by
      have := hqt
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    calc q * g₁ * t = q * (g₁ * t) := by rw [mul_assoc]
      _ = q * (t * g₁) := by rw [h1]
      _ = (q * t) * g₁ := by rw [mul_assoc]
      _ = (t * q) * g₁ := by rw [h2]
      _ = t * (q * g₁) := by rw [mul_assoc]
  · rw [show q * p₁ * g = q * g₁ by rw [hg₁, mul_assoc]]
    calc q * g₁ * y * (q * g₁)⁻¹ = q * (g₁ * y * g₁⁻¹) * q⁻¹ := by group
      _ = y' := by rw [← hy₁def, hqy]

end LeechSystem

end CFSG.Monster.GMS
