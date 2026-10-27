module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.DISTX

open Equiv Equiv.Perm

theorem involution_swap_or_even : ∀ x : Perm (Fin 4), x * x = 1 → x ≠ 1 →
    (∃ a b, a ≠ b ∧ x = swap a b) ∨ Perm.sign x = 1 := by decide +kernel

theorem exists_conj_order_four : ∀ x w : Perm (Fin 4), x * x = 1 → x ≠ 1 →
    (¬ ∃ a b, a ≠ b ∧ x = swap a b) → (∃ a b, a ≠ b ∧ w = swap a b) →
    ∃ g : Perm (Fin 4), (w * (g * x * g⁻¹)) ^ 6 ≠ 1 := by decide +kernel

theorem swap_conj : ∀ z w : Perm (Fin 4), (∃ a b, a ≠ b ∧ z = swap a b) →
    (∃ a b, a ≠ b ∧ w = swap a b) → ∃ g : Perm (Fin 4), g * w * g⁻¹ = z := by decide +kernel

theorem swap_commute_cases : ∀ a b : Perm (Fin 4), (∃ i j, i ≠ j ∧ a = swap i j) →
    (∃ i j, i ≠ j ∧ b = swap i j) → b * a = a * b →
    b = a ∨ ∃ x z : Perm (Fin 4), (∃ i j, i ≠ j ∧ x = swap i j) ∧ (∃ i j, i ≠ j ∧ z = swap i j) ∧
      x * a ≠ a * x ∧ z * a ≠ a * z ∧ b = x * z * x⁻¹ := by decide +kernel

theorem pow_six_eq_one_of_orderOf_le {M : Type*} [Group M] [Finite M] {z : M}
    (h : orderOf z ≤ 3) : z ^ 6 = 1 := by
  have hpos : 0 < orderOf z := orderOf_pos z
  have hcases : orderOf z = 1 ∨ orderOf z = 2 ∨ orderOf z = 3 := by omega
  have hd : orderOf z ∣ 6 := by
    rcases hcases with h1 | h1 | h1 <;> rw [h1] <;> decide
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem perm4_classify (R : Set (Perm (Fin 4))) (h1 : ∀ x ∈ R, x * x = 1 ∧ x ≠ 1)
    (h2 : ∀ g x, x ∈ R → g * x * g⁻¹ ∈ R) (h3 : Subgroup.closure R = ⊤)
    (h4 : ∀ x ∈ R, ∀ y ∈ R, orderOf (x * y) ≤ 3) :
    ∀ x, x ∈ R ↔ ∃ a b, a ≠ b ∧ x = swap a b := by
  have hsw : ∃ w ∈ R, ∃ a b, a ≠ b ∧ w = swap a b := by
    by_contra hno
    push Not at hno
    have hle : Subgroup.closure R ≤ (Perm.sign : Perm (Fin 4) →* ℤˣ).ker := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨hx2, hx1⟩ := h1 x hx
      rcases involution_swap_or_even x hx2 hx1 with ⟨a, b, hab, hxab⟩ | hs
      · exact absurd hxab (hno x hx a b hab)
      · exact hs
    rw [h3] at hle
    have hmem : (swap (0 : Fin 4) 1) ∈ (Perm.sign : Perm (Fin 4) →* ℤˣ).ker :=
      hle (Subgroup.mem_top _)
    rw [MonoidHom.mem_ker, sign_swap (by decide)] at hmem
    exact absurd hmem (by decide)
  obtain ⟨w, hwR, hwsw⟩ := hsw
  have hnoDouble : ∀ x ∈ R, ∃ a b, a ≠ b ∧ x = swap a b := by
    intro x hx
    by_contra hnx
    obtain ⟨hx2, hx1⟩ := h1 x hx
    obtain ⟨g, hg⟩ := exists_conj_order_four x w hx2 hx1 hnx hwsw
    apply hg
    exact pow_six_eq_one_of_orderOf_le (h4 w hwR _ (h2 g x hx))
  intro x
  constructor
  · exact hnoDouble x
  · intro hx
    obtain ⟨g, hg⟩ := swap_conj x w hx hwsw
    rw [← hg]
    exact h2 g w hwR

variable {Γ : Type*} [Group Γ]

theorem mem_iff_swap (ψ : Γ ≃* Perm (Fin 4)) (R : Set Γ) (h1 : ∀ x ∈ R, x * x = 1 ∧ x ≠ 1)
    (h2 : ∀ g x, x ∈ R → g * x * g⁻¹ ∈ R) (h3 : Subgroup.closure R = ⊤)
    (h4 : ∀ x ∈ R, ∀ y ∈ R, orderOf (x * y) ≤ 3) :
    ∀ x, x ∈ R ↔ ∃ a b, a ≠ b ∧ ψ x = swap a b := by
  have key := perm4_classify (ψ '' R) ?_ ?_ ?_ ?_
  · intro x
    rw [← key (ψ x), Set.mem_image]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => ψ.injective hyx ▸ hy⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hx2, hx1⟩ := h1 x hx
    refine ⟨by rw [← map_mul, hx2, map_one], fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm))⟩
  · rintro g _ ⟨x, hx, rfl⟩
    refine ⟨ψ.symm g * x * (ψ.symm g)⁻¹, h2 _ x hx, ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · have h := MonoidHom.map_closure ψ.toMonoidHom R
    rw [h3, Subgroup.map_top] at h
    exact h.symm.trans (MonoidHom.range_eq_top.mpr ψ.surjective)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h4 x hx y hy

theorem exists_conj_of_mem (ψ : Γ ≃* Perm (Fin 4)) (R : Set Γ) (h1 : ∀ x ∈ R, x * x = 1 ∧ x ≠ 1)
    (h2 : ∀ g x, x ∈ R → g * x * g⁻¹ ∈ R) (h3 : Subgroup.closure R = ⊤)
    (h4 : ∀ x ∈ R, ∀ y ∈ R, orderOf (x * y) ≤ 3) {x y : Γ} (hx : x ∈ R) (hy : y ∈ R) :
    ∃ g : Γ, g * x * g⁻¹ = y := by
  have hc := mem_iff_swap ψ R h1 h2 h3 h4
  obtain ⟨g, hg⟩ := swap_conj (ψ y) (ψ x) ((hc y).mp hy) ((hc x).mp hx)
  refine ⟨ψ.symm g, ψ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg

theorem exists_cases_of_commute (ψ : Γ ≃* Perm (Fin 4)) (R : Set Γ)
    (h1 : ∀ x ∈ R, x * x = 1 ∧ x ≠ 1) (h2 : ∀ g x, x ∈ R → g * x * g⁻¹ ∈ R)
    (h3 : Subgroup.closure R = ⊤) (h4 : ∀ x ∈ R, ∀ y ∈ R, orderOf (x * y) ≤ 3) {t y : Γ}
    (ht : t ∈ R) (hy : y ∈ R) (hcomm : y * t = t * y) :
    y = t ∨ ∃ x ∈ R, ∃ z ∈ R, x * t ≠ t * x ∧ z * t ≠ t * z ∧ y = x * z * x⁻¹ := by
  have hc := mem_iff_swap ψ R h1 h2 h3 h4
  have hcomm' : ψ y * ψ t = ψ t * ψ y := by rw [← map_mul, ← map_mul, hcomm]
  rcases swap_commute_cases (ψ t) (ψ y) ((hc t).mp ht) ((hc y).mp hy) hcomm' with h | ⟨x, z, hx,
  hz, hxt, hzt, hyxz⟩
  · exact Or.inl (ψ.injective h)
  · refine Or.inr ⟨ψ.symm x, ?_, ψ.symm z, ?_, ?_, ?_, ?_⟩
    · rw [hc]
      obtain ⟨a, b, hab, hxab⟩ := hx
      exact ⟨a, b, hab, by rw [MulEquiv.apply_symm_apply]; exact hxab⟩
    · rw [hc]
      obtain ⟨a, b, hab, hzab⟩ := hz
      exact ⟨a, b, hab, by rw [MulEquiv.apply_symm_apply]; exact hzab⟩
    · intro h
      apply hxt
      have := congrArg ψ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro h
      apply hzt
      have := congrArg ψ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · apply ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hyxz

end CFSG.RankThree.PartOne.DISTX
