module

public import CFSG.Quasithin.EmptyFaithful.S153EGen
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace S153EN8

variable {G : Type*} [Group G]

theorem exists_mul_mem_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {D Q : Subgroup G}
    (hDp : IsPGroup p D) (hDQ : D ⊓ Q = ⊥) (hQD : D ≤ Subgroup.normalizer (Q : Set G))
    (hsyl : ¬ p ∣ D.relIndex (D ⊔ Q)) {x : G} (hx : ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ Q) :
    ∃ q ∈ Q, q⁻¹ * x ∈ Subgroup.centralizer (D : Set G) := by
  have hP : D ≤ D ⊔ Q ∧ IsPGroup p D ∧ ¬ p ∣ D.relIndex (D ⊔ Q) := ⟨le_sup_left, hDp, hsyl⟩
  have hR : IsPGroup p (conjSubgroup D x⁻¹) := S153E.isPGroup_conjSubgroup153 hDp x⁻¹
  have hRK : conjSubgroup D x⁻¹ ≤ D ⊔ Q := by
    intro r hr
    rw [mem_conjSubgroup_iff] at hr
    have h1 : x⁻¹ * r * x⁻¹⁻¹ ∈ D := hr
    simp only [inv_inv] at h1
    have e : r = (x * (x⁻¹ * r * x) * x⁻¹ * (x⁻¹ * r * x)⁻¹) * (x⁻¹ * r * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hx _ h1)) (Subgroup.mem_sup_left h1)
  obtain ⟨k, hkK, hk⟩ := S153E.exists_conj_of_isSylow hP hR hRK
  have hk' : k ∈ ((D ⊔ Q : Subgroup G) : Set G) := hkK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D Q hQD] at hk'
  obtain ⟨d₀, hd₀, q₀, hq₀, rfl⟩ := hk'
  refine ⟨q₀⁻¹, Q.inv_mem hq₀, ?_⟩
  rw [inv_inv]
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 : d₀ * q₀ * (x * d * x⁻¹) * (d₀ * q₀)⁻¹ ∈ D := by
    have := hk (show x * d * x⁻¹ ∈ conjSubgroup D x⁻¹ from by
      rw [mem_conjSubgroup_iff]
      have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
      rw [e]
      exact hd)
    rw [mem_conjSubgroup_iff] at this
    exact this
  have h2 : q₀ * (x * d * x⁻¹) * q₀⁻¹ ∈ D := by
    have e : q₀ * (x * d * x⁻¹) * q₀⁻¹ =
        d₀⁻¹ * (d₀ * q₀ * (x * d * x⁻¹) * (d₀ * q₀)⁻¹) * d₀ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (D.inv_mem hd₀) h1) hd₀
  have h3 : q₀ * (x * d * x⁻¹) * q₀⁻¹ * d⁻¹ ∈ D := D.mul_mem h2 (D.inv_mem hd)
  have h4 : q₀ * (x * d * x⁻¹) * q₀⁻¹ * d⁻¹ ∈ Q := by
    have e : q₀ * (x * d * x⁻¹) * q₀⁻¹ * d⁻¹ =
        q₀ * (x * d * x⁻¹ * d⁻¹) * (d * q₀⁻¹ * d⁻¹) := by group
    rw [e]
    refine Q.mul_mem (Q.mul_mem hq₀ (hx d hd)) ?_
    have := (Subgroup.mem_normalizer_iff.mp (hQD hd) q₀⁻¹).mp (Q.inv_mem hq₀)
    exact this
  have h5 : q₀ * (x * d * x⁻¹) * q₀⁻¹ * d⁻¹ = 1 := by
    have : q₀ * (x * d * x⁻¹) * q₀⁻¹ * d⁻¹ ∈ D ⊓ Q := ⟨h3, h4⟩
    rw [hDQ] at this
    exact Subgroup.mem_bot.mp this
  have h6 : q₀ * x * d * (q₀ * x)⁻¹ = d := by
    have := mul_inv_eq_one.mp h5
    calc q₀ * x * d * (q₀ * x)⁻¹ = q₀ * (x * d * x⁻¹) * q₀⁻¹ := by group
      _ = d := this
  calc d * (q₀ * x) = (q₀ * x * d * (q₀ * x)⁻¹) * (q₀ * x) := by rw [h6]
    _ = (q₀ * x) * d := by group

end S153EN8

end CFSG.Quasithin
