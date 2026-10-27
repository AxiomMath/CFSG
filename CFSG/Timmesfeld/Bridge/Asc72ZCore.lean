module

public import CFSG.Timmesfeld.Bridge.Asc72ZQuot
public import CFSG.Timmesfeld.Bridge.Asc72ZAlt

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.Asc72.AltFive

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_localSet (hN : IsNormalSet D) {z : G} (k : localGroup D z)
    {x : localGroup D z} (hx : x ∈ localSet D z) : k * x * k⁻¹ ∈ localSet D z := by
  have hkz := commute_of_mem_localGroup k.2
  show ((k : G) * x * (k : G)⁻¹) ∈ centSet D z
  exact ⟨hN k x hx.1, (hkz.mul_left hx.2).mul_left hkz.inv_left⟩

section Core

variable (hD : IsOddTransp D) (hN : IsNormalSet D) {z : G}
  (ρ : localGroup D z →* alternatingGroup (Fin 5)) (hρ : Function.Surjective ρ)
  (hinj : ∀ x y : localGroup D z, x ∈ localSet D z → y ∈ localSet D z → ρ x = ρ y → x = y)
  (hcomm : ∀ x y : localGroup D z, x ∈ localSet D z → y ∈ localSet D z →
    Commute (ρ x) (ρ y) → Commute x y)
  {c : localGroup D z} (hc : c ∈ localSet D z) (hρc : ρ c = c0)

include hD hN hρ hinj hcomm hc hρc in
theorem reach_of_spread {γ : localGroup D z} (hγ : γ ∈ localSet D z)
    (hργ : ρ γ = o1 ∨ ρ γ = o3) (hreach : Reach D (c : G) (γ : G)) {y : localGroup D z}
    (hy : y ∈ localSet D z) : Reach D (c : G) (y : G) := by
  have hyy : ρ y * ρ y = 1 := by
    rw [← map_mul, show y * y = 1 from Subtype.ext (hD.mul_self_eq_one hy.1), map_one]
  rcases spread hργ (ρ y) hyy with h | ⟨t, ht, hyt⟩
  · have h1 : Commute y c := hcomm y c hy hc (by rw [hρc]; exact h)
    exact reach_of_commute hc.1 hy.1 (commute_coe_iff.mpr h1.symm)
  · obtain ⟨k, rfl⟩ := hρ t
    have hkc : k * c * k⁻¹ = c := hinj _ _ (conj_mem_localSet hN k hc) hc (by
      rw [map_mul, map_mul, map_inv, hρc, ht, mul_inv_cancel_right])
    have h1 := reach_conj hN (k : G) hreach
    have h2 : (k : G) * c * (k : G)⁻¹ = c := congrArg Subtype.val hkc
    rw [h2] at h1
    have h3 : Commute y (k * γ * k⁻¹) := hcomm _ _ hy (conj_mem_localSet hN k hγ) (by
      rw [map_mul, map_mul, map_inv]
      exact hyt)
    exact reach_trans h1 (reach_of_commute (conj_mem_localSet hN k hγ).1 hy.1
      (commute_coe_iff.mpr h3).symm)

include hN hρ hinj hc hρc in
theorem exists_gamma {a : G} (haz : Commute a z) (φ : MulAut (localGroup D z))
    (hφ : ∀ x, (φ x : G) = a * x * a⁻¹) (ψ : MulAut (alternatingGroup (Fin 5)))
    (hρφ : ∀ x, ρ (φ x) = ψ (ρ x)) {γA kA : alternatingGroup (Fin 5)}
    (hγA : γA = o1 ∨ γA = o3) (hψγ : ψ γA = γA) (hk : kA * c0 * kA⁻¹ = γA) :
    ∃ γ : localGroup D z, γ ∈ localSet D z ∧ Commute a (γ : G) ∧ ¬ Commute (c : G) (γ : G) ∧
      ρ γ = γA := by
  obtain ⟨k, rfl⟩ := hρ kA
  have hγ := conj_mem_localSet hN k hc
  have hργ : ρ (k * c * k⁻¹) = γA := by rw [map_mul, map_mul, map_inv, hρc, hk]
  have hφγ : φ (k * c * k⁻¹) ∈ localSet D z := by
    show ((φ (k * c * k⁻¹) : localGroup D z) : G) ∈ centSet D z
    rw [hφ]
    exact ⟨hN a _ hγ.1, (haz.mul_left hγ.2).mul_left haz.inv_left⟩
  have hfix : φ (k * c * k⁻¹) = k * c * k⁻¹ := hinj _ _ hφγ hγ (by rw [hρφ, hργ, hψγ])
  refine ⟨k * c * k⁻¹, hγ, ?_, fun h => ?_, hργ⟩
  · have h1 : a * ((k * c * k⁻¹ : localGroup D z) : G) * a⁻¹ =
        ((k * c * k⁻¹ : localGroup D z) : G) := by
      rw [← hφ, hfix]
    show a * _ = _ * a
    calc a * ((k * c * k⁻¹ : localGroup D z) : G)
        = a * ((k * c * k⁻¹ : localGroup D z) : G) * a⁻¹ * a := by group
      _ = ((k * c * k⁻¹ : localGroup D z) : G) * a := by rw [h1]
  · have h1 : Commute (ρ c) (ρ (k * c * k⁻¹)) := (commute_coe_iff.mp h).map ρ
    rw [hρc, hργ] at h1
    exact not_commute_c0 hγA h1.eq.symm

include hρ in
theorem exists_conj_mul {a : G} (haa : a * a = 1) (φ : MulAut (localGroup D z))
    (hφ : ∀ x, (φ x : G) = a * x * a⁻¹) (ψ : MulAut (alternatingGroup (Fin 5)))
    (hρφ : ∀ x, ρ (φ x) = ψ (ρ x)) (hx0 : x0 * ψ x0⁻¹ * c0 = 1)
    (hker : ∀ p : localGroup D z, ρ p = 1 →
      ∃ m : ℕ, Odd m ∧ ((p : G) ^ m = 1 ∨ (p : G) ^ m = z))
    {c : localGroup D z} (hρc : ρ c = c0) (hac : Commute a (c : G)) (hcc : (c : G) * c = 1) :
    ∃ g : G, g * (a * c) * g⁻¹ = a ∨ g * (a * c) * g⁻¹ = a * z := by
  obtain ⟨h, hh⟩ := hρ x0
  set p : localGroup D z := h * φ h⁻¹ * c with hpdef
  have hρp : ρ p = 1 := by rw [hpdef, map_mul, map_mul, hρφ, map_inv, hh, hρc, hx0]
  obtain ⟨m, hm, hpm⟩ := hker p hρp
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set s := (h : G) * a * (h : G)⁻¹ with hsdef
  set t := a * (c : G) with htdef
  have hss : s * s = 1 := by
    rw [hsdef, show (h : G) * a * (h : G)⁻¹ * ((h : G) * a * (h : G)⁻¹) =
      (h : G) * (a * a) * (h : G)⁻¹ by group, haa, mul_one, mul_inv_cancel]
  have htt : t * t = 1 := by
    rw [htdef, show a * (c : G) * (a * c) = a * (c * a) * c by group, ← hac.eq,
      show a * (a * (c : G)) * c = (a * a) * (c * c) by group, haa, hcc, one_mul]
  have hp : (p : G) = s * t := by
    rw [hpdef, Subgroup.coe_mul, Subgroup.coe_mul, hφ, Subgroup.coe_inv, hsdef, htdef, hai]
    group
  obtain ⟨k, rfl⟩ := hm
  have key := inv_pow_mul_mul_pow hss htt k
  rw [← hp] at key
  have hhz : Commute (h : G) z := commute_of_mem_localGroup h.2
  have hconj : (h : G)⁻¹ * ((p : G) ^ k)⁻¹ * t * ((h : G)⁻¹ * ((p : G) ^ k)⁻¹)⁻¹ =
      (h : G)⁻¹ * (((p : G) ^ k)⁻¹ * t * (p : G) ^ k) * h := by group
  refine ⟨(h : G)⁻¹ * ((p : G) ^ k)⁻¹, ?_⟩
  rcases hpm with h1 | h1
  · left
    rw [h1, mul_one] at key
    rw [hconj, key, hsdef]
    group
  · right
    rw [h1] at key
    have hz' : (h : G)⁻¹ * z * h = z := by rw [mul_assoc, ← hhz.eq, inv_mul_cancel_left]
    rw [hconj, key, hsdef, show (h : G)⁻¹ * ((h : G) * a * (h : G)⁻¹ * z) * h =
      a * ((h : G)⁻¹ * z * h) by group, hz']

end Core

end CFSG.Timmesfeld.Bridge.Asc72
