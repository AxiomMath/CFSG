module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.FixedData

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut

open UnitaryFrame (FixedData)

variable {Y : Type*} [Group Y] {C P : Subgroup Y}

theorem comm_P (hF : FixedData C P) {x y : Y} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P)
    (by rw [hF.card_P]; norm_num)
  exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem exists_ne_one (hF : FixedData C P) : ∃ x ∈ P, x ≠ 1 := by
  by_contra h
  push Not at h
  have : Nat.card P = 1 := Subgroup.card_eq_one.mpr ((Subgroup.eq_bot_iff_forall _).mpr h)
  rw [hF.card_P] at this
  omega


theorem conj_eq_inv (hF : FixedData C P) {u : Y} (huC : u ∈ C) (huP : u ∉ P) (hu : u * u = 1)
    {x : Y} (hx : x ∈ P) : u * x * u⁻¹ = x⁻¹ := by
  have hui : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu, inv_one]
  have hvP : u * x * u⁻¹ ∈ P := hF.normalizes u huC x hx
  have h1 : x * (u * x * u⁻¹) = (u * x * u⁻¹) * x := comm_P hF hx hvP
  have hv : u * (u * x * u⁻¹) * u⁻¹ = x := by
    calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
      _ = x := by rw [hu, hui]; group
  have hconj : u * (x * (u * x * u⁻¹)) * u⁻¹ = x * (u * x * u⁻¹) := by
    calc u * (x * (u * x * u⁻¹)) * u⁻¹ = (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) := by group
      _ = (u * x * u⁻¹) * x := by rw [hv]
      _ = x * (u * x * u⁻¹) := h1.symm
  have hcomm : u * (x * (u * x * u⁻¹)) = (x * (u * x * u⁻¹)) * u :=
    mul_inv_eq_iff_eq_mul.mp hconj
  by_contra hne
  have hw1 : x * (u * x * u⁻¹) ≠ 1 := fun h => hne (eq_inv_of_mul_eq_one_right h)
  exact huP (hF.mem_of_commute u huC _ (Subgroup.mul_mem _ hx hvP) hw1 hcomm)


theorem exists_involution (hF : FixedData C P) : ∃ z ∈ C, z ∉ P ∧ z * z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hF.card_C]; norm_num)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by rw [hF.card_C]; norm_num)
  have hz2 : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe, hz]
  refine ⟨z, z.2, fun hzP => ?_, ?_⟩
  · have h1 : orderOf (z : Y) ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard P hzP
      rwa [hF.card_P] at this
    rw [hz2] at h1
    omega
  · rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one _

section Involution

variable (hF : FixedData C P) {z : Y} (hzC : z ∈ C) (hzP : z ∉ P) (hz : z * z = 1)
include hF hzC hzP hz

theorem inv_mul_conj_mem {c : Y} (hc : c ∈ C) : z⁻¹ * (c * z * c⁻¹) ∈ P := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have huC : c * z * c⁻¹ ∈ C := Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hzC)
    (Subgroup.inv_mem _ hc)
  have huP : c * z * c⁻¹ ∉ P := by
    intro h
    apply hzP
    have := hF.normalizes c⁻¹ (Subgroup.inv_mem _ hc) _ h
    simpa [mul_assoc] using this
  have hu : (c * z * c⁻¹) * (c * z * c⁻¹) = 1 := by
    calc (c * z * c⁻¹) * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz]; group
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one hF
  have hcomm : z⁻¹ * (c * z * c⁻¹) * x₀ = x₀ * (z⁻¹ * (c * z * c⁻¹)) := by
    have h1 := conj_eq_inv hF huC huP hu hx₀
    have h2 := conj_eq_inv hF hzC hzP hz hx₀
    have h3 : z⁻¹ * (c * z * c⁻¹) * x₀ * (z⁻¹ * (c * z * c⁻¹))⁻¹ = x₀ := by
      have e1 : z⁻¹ * (c * z * c⁻¹) * x₀ * (z⁻¹ * (c * z * c⁻¹))⁻¹ =
          z⁻¹ * ((c * z * c⁻¹) * x₀ * (c * z * c⁻¹)⁻¹) * z⁻¹⁻¹ := by group
      rw [e1, h1, inv_inv, hzi]
      calc z * x₀⁻¹ * z = z * x₀⁻¹ * z⁻¹ := by rw [hzi]
        _ = (z * x₀ * z⁻¹)⁻¹ := by group
        _ = x₀ := by rw [h2, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp h3
  have hwC : z⁻¹ * (c * z * c⁻¹) ∈ C := Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) huC
  exact hF.mem_of_commute _ hwC x₀ hx₀ hx₀1 hcomm

theorem conj_eq_mul {w : Y} (hw : w ∈ P) : w * z * w⁻¹ = z * w := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h1 : z * w⁻¹ * z⁻¹ = w := by
    rw [conj_eq_inv hF hzC hzP hz (Subgroup.inv_mem _ hw), inv_inv]
  have h3 : w * w * w = 1 := by
    have := hF.pow_three w hw
    simpa [pow_succ] using this
  have h4 : w⁻¹ * w⁻¹ = w := by
    calc w⁻¹ * w⁻¹ = w⁻¹ * w⁻¹ * (w * w * w) := by rw [h3, mul_one]
      _ = w := by group
  calc w * z * w⁻¹ = z * (z⁻¹ * w * z) * w⁻¹ := by group
    _ = z * (z * w * z⁻¹) * w⁻¹ := by rw [hzi]
    _ = z * w⁻¹ * w⁻¹ := by rw [conj_eq_inv hF hzC hzP hz hw]
    _ = z * w := by rw [mul_assoc, h4]

theorem eq_one_of_commute {x : Y} (hx : x ∈ P) (hxz : z * x = x * z) : x = 1 := by
  have h1 := conj_eq_inv hF hzC hzP hz hx
  have h2 : z * x * z⁻¹ = x := by rw [hxz]; group
  have hxx : x * x = 1 := by
    have h3 : x = x⁻¹ := h2.symm.trans h1
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x
  have h3 : x * x * x = 1 := by simpa [pow_succ] using hF.pow_three x hx
  calc x = x * x * x * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, hxx]; simp

theorem exists_mul_of_mem {c : Y} (hc : c ∈ C) :
    ∃ w ∈ P, ∃ q ∈ C, z * q = q * z ∧ c = w * q := by
  have hwP := inv_mul_conj_mem hF hzC hzP hz hc
  set w := z⁻¹ * (c * z * c⁻¹) with hw
  have hcz : c * z * c⁻¹ = w * z * w⁻¹ := by
    rw [conj_eq_mul hF hzC hzP hz hwP, hw]
    group
  refine ⟨w, hwP, w⁻¹ * c, Subgroup.mul_mem _ (Subgroup.inv_mem _ (hF.le hwP)) hc, ?_, by group⟩
  have : (w⁻¹ * c) * z * (w⁻¹ * c)⁻¹ = z := by
    calc (w⁻¹ * c) * z * (w⁻¹ * c)⁻¹ = w⁻¹ * (c * z * c⁻¹) * w := by group
      _ = w⁻¹ * (w * z * w⁻¹) * w := by rw [hcz]
      _ = z := by group
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

theorem fixes_of_fixes_involution (g : MulAut Y) (hgP : ∀ c ∈ C, c⁻¹ * g c ∈ P)
    (hgPfix : ∀ x ∈ P, g x = x) (hgz : g z = z) : ∀ c ∈ C, g c = c := by
  intro c hc
  obtain ⟨w, hw, q, hq, hzq, rfl⟩ := exists_mul_of_mem hF hzC hzP hz hc
  have hgq : g q = q := by
    have h1 : z * g q = g q * z := by
      have := congrArg g hzq
      rwa [map_mul, map_mul, hgz] at this
    have h2 : q⁻¹ * g q ∈ P := hgP q hq
    have h4 : z * q⁻¹ = q⁻¹ * z := (Commute.inv_right (show Commute z q from hzq)).eq
    have h3 : z * (q⁻¹ * g q) = (q⁻¹ * g q) * z := by
      calc z * (q⁻¹ * g q) = (z * q⁻¹) * g q := by group
        _ = (q⁻¹ * z) * g q := by rw [h4]
        _ = q⁻¹ * (z * g q) := by group
        _ = q⁻¹ * (g q * z) := by rw [h1]
        _ = (q⁻¹ * g q) * z := by group
    exact (inv_mul_eq_one.mp (eq_one_of_commute hF hzC hzP hz h2 h3)).symm
  rw [map_mul, hgPfix w hw, hgq]

end Involution

theorem exists_conj_of_fixes (hF : FixedData C P) (g : MulAut Y) (hgC : ∀ c ∈ C, g c ∈ C)
    (hgPfix : ∀ x ∈ P, g x = x) : ∃ u ∈ P, ∀ c ∈ C, g c = u * c * u⁻¹ := by
  obtain ⟨z, hzC, hzP, hz⟩ := exists_involution hF
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one hF
  have hgP : ∀ c ∈ C, c⁻¹ * g c ∈ P := by
    intro c hc
    have hv : (c⁻¹ * g c) * x₀ = x₀ * (c⁻¹ * g c) := by
      have h1 : g (c * x₀ * c⁻¹) = c * x₀ * c⁻¹ := hgPfix _ (hF.normalizes c hc x₀ hx₀)
      rw [map_mul, map_mul, map_inv, hgPfix x₀ hx₀] at h1
      calc (c⁻¹ * g c) * x₀ = c⁻¹ * (g c * x₀ * (g c)⁻¹) * g c := by group
        _ = c⁻¹ * (c * x₀ * c⁻¹) * g c := by rw [h1]
        _ = x₀ * (c⁻¹ * g c) := by group
    exact hF.mem_of_commute _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (hgC c hc)) x₀ hx₀
      hx₀1 hv
  set u := z⁻¹ * g z with hu_def
  have huP : u ∈ P := hgP z hzC
  have hgz : g z = u * z * u⁻¹ := by
    rw [conj_eq_mul hF hzC hzP hz huP, hu_def]
    group
  set g₃ : MulAut Y := MulAut.conj u⁻¹ * g with hg₃
  have hg₃apply : ∀ y, g₃ y = u⁻¹ * g y * u := by
    intro y
    simp [hg₃]
  have hg₃P : ∀ x ∈ P, g₃ x = x := by
    intro x hx
    rw [hg₃apply, hgPfix x hx]
    have := comm_P hF hx huP
    calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
      _ = u⁻¹ * (u * x) := by rw [this]
      _ = x := by group
  have hg₃z : g₃ z = z := by
    rw [hg₃apply, hgz]
    group
  have hg₃P' : ∀ c ∈ C, c⁻¹ * g₃ c ∈ P := by
    intro c hc
    rw [hg₃apply]
    have h1 : c⁻¹ * u⁻¹ * c ∈ P := by
      have := hF.normalizes c⁻¹ (Subgroup.inv_mem _ hc) u⁻¹ (Subgroup.inv_mem _ huP)
      simpa using this
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (hgP c hc)) huP
    have h3 : c⁻¹ * (u⁻¹ * g c * u) = (c⁻¹ * u⁻¹ * c) * (c⁻¹ * g c) * u := by group
    rw [h3]
    exact h2
  have key := fixes_of_fixes_involution hF hzC hzP hz g₃ hg₃P' hg₃P hg₃z
  refine ⟨u, huP, fun c hc => ?_⟩
  have := key c hc
  rw [hg₃apply] at this
  calc g c = u * (u⁻¹ * g c * u) * u⁻¹ := by group
    _ = u * c * u⁻¹ := by rw [this]


theorem apply_conj_of_trivial_mod (hF : FixedData C P) (g : MulAut Y)
    (hgP : ∀ c ∈ C, c⁻¹ * g c ∈ P) {c x : Y} (hc : c ∈ C) (hx : x ∈ P) :
    g (c * x * c⁻¹) = c * g x * c⁻¹ := by
  have hgx : g x ∈ P := by
    have := Subgroup.mul_mem _ hx (hgP x (hF.le hx))
    simpa using this
  have hw : c⁻¹ * g c ∈ P := hgP c hc
  have hcomm := comm_P hF hw hgx
  have h1 : g c = c * (c⁻¹ * g c) := by group
  rw [map_mul, map_mul, map_inv, h1]
  calc c * (c⁻¹ * g c) * g x * (c * (c⁻¹ * g c))⁻¹
      = c * ((c⁻¹ * g c) * g x * (c⁻¹ * g c)⁻¹) * c⁻¹ := by group
    _ = c * g x * c⁻¹ := by rw [hcomm]; group

theorem exists_conj_on (hF : FixedData C P) (g : MulAut Y) (hgP : ∀ c ∈ C, c⁻¹ * g c ∈ P) :
    ∃ c₁ ∈ C, ∀ x ∈ P, g x = c₁ * x * c₁⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzC, hzP, hz⟩ := exists_involution hF
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one hF
  have hgP' : ∀ x ∈ P, g x ∈ P := fun x hx => by
    have := Subgroup.mul_mem _ hx (hgP x (hF.le hx))
    simpa using this
  have hy1 : g x₀ ≠ 1 := fun h => hx₀1 (g.injective (by rw [h, map_one]))
  have hord : orderOf x₀ = 3 := orderOf_eq_prime (hF.pow_three x₀ hx₀) hx₀1
  by_cases hy : g x₀ ∈ Subgroup.zpowers x₀
  ·
    have hcases : g x₀ = x₀ ∨ g x₀ = x₀⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk3 : x₀ ^ (k % 3) = g x₀ := by
        have := zpow_mod_orderOf x₀ k
        rw [hord] at this
        rw [← hk]
        simpa using this
      have h3 : x₀ * x₀ * x₀ = 1 := by simpa [pow_succ] using hF.pow_three x₀ hx₀
      have hk' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk' with h0 | h1 | h2
      · exact absurd (by rw [← hk3, h0, zpow_zero]) hy1
      · left
        rw [← hk3, h1, zpow_one]
      · right
        rw [← hk3, h2]
        calc x₀ ^ (2 : ℤ) = x₀ * x₀ := by rw [zpow_two]
          _ = x₀⁻¹ := eq_inv_of_mul_eq_one_left h3
    rcases hcases with h | h
    · refine ⟨1, one_mem C, fun x hx => ?_⟩
      by_cases hx1 : x = 1
      · simp [hx1]
      · obtain ⟨c, hc, hcx⟩ := hF.trans x₀ hx₀ hx₀1 x hx hx1
        rw [← hcx, apply_conj_of_trivial_mod hF g hgP hc hx₀, h]
        group
    · refine ⟨z, hzC, fun x hx => ?_⟩
      by_cases hx1 : x = 1
      · simp [hx1]
      · obtain ⟨c, hc, hcx⟩ := hF.trans x₀ hx₀ hx₀1 x hx hx1
        rw [conj_eq_inv hF hzC hzP hz hx, ← hcx, apply_conj_of_trivial_mod hF g hgP hc hx₀, h]
        group
  · obtain ⟨c₀, hc₀, hc₀x⟩ := hF.trans x₀ hx₀ hx₀1 (g x₀) (hgP' x₀ hx₀) hy1
    refine ⟨c₀, hc₀, fun x hx => ?_⟩
    have hHle : Subgroup.closure {x₀, g x₀} ≤ P := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hx₀
      · exact hgP' x₀ hx₀
    have hfinP : Finite P := Nat.finite_of_card_ne_zero (by rw [hF.card_P]; norm_num)
    have hfinH : Finite (Subgroup.closure {x₀, g x₀}) :=
      Finite.of_injective (Subgroup.inclusion hHle) (Subgroup.inclusion_injective hHle)
    have hzH : Subgroup.zpowers x₀ ≤ Subgroup.closure {x₀, g x₀} :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h3 : 3 ∣ Nat.card (Subgroup.closure {x₀, g x₀}) := by
      have := Subgroup.card_dvd_of_le hzH
      rwa [Nat.card_zpowers, hord] at this
    have h9 : Nat.card (Subgroup.closure {x₀, g x₀}) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hHle
      rwa [hF.card_P] at this
    have hne3 : Nat.card (Subgroup.closure {x₀, g x₀}) ≠ 3 := by
      intro h
      apply hy
      have : Subgroup.zpowers x₀ = Subgroup.closure {x₀, g x₀} :=
        Subgroup.eq_of_le_of_card_ge hzH (by rw [h, Nat.card_zpowers, hord])
      rw [this]
      exact Subgroup.subset_closure (by simp)
    have h99 : Nat.card (Subgroup.closure {x₀, g x₀}) = 9 := by
      have hmem : Nat.card (Subgroup.closure {x₀, g x₀}) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.mpr ⟨h9, by norm_num⟩
      have e : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [e] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    have hcl : Subgroup.closure {x₀, g x₀} = P :=
      Subgroup.eq_of_le_of_card_ge hHle (by rw [h99, hF.card_P])
    have heq : Set.EqOn (g : Y →* Y) (MulAut.conj c₀ : Y →* Y)
        (Subgroup.closure {x₀, g x₀}) := by
      apply MonoidHom.eqOn_closure
      rintro _ (rfl | rfl)
      · exact hc₀x.symm
      · have e := apply_conj_of_trivial_mod hF g hgP hc₀ hx₀
        rw [hc₀x] at e
        exact e
    exact heq (hcl ▸ hx)


theorem exists_conj_of_trivial_mod (hF : FixedData C P) (g : MulAut Y)
    (hgC : ∀ c ∈ C, g c ∈ C) (hgP : ∀ c ∈ C, c⁻¹ * g c ∈ P) :
    ∃ c ∈ C, ∀ x ∈ C, g x = c * x * c⁻¹ := by
  obtain ⟨c₁, hc₁, h1⟩ := exists_conj_on hF g hgP
  set g₂ : MulAut Y := MulAut.conj c₁⁻¹ * g with hg₂
  have hg₂apply : ∀ y, g₂ y = c₁⁻¹ * g y * c₁ := by
    intro y
    simp [hg₂]
  have hg₂P : ∀ x ∈ P, g₂ x = x := by
    intro x hx
    rw [hg₂apply, h1 x hx]
    group
  have hg₂C : ∀ c ∈ C, g₂ c ∈ C := fun c hc => by
    rw [hg₂apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₁) (hgC c hc)) hc₁
  obtain ⟨u, hu, h2⟩ := exists_conj_of_fixes hF g₂ hg₂C hg₂P
  refine ⟨c₁ * u, Subgroup.mul_mem _ hc₁ (hF.le hu), fun x hx => ?_⟩
  have := h2 x hx
  rw [hg₂apply] at this
  calc g x = c₁ * (c₁⁻¹ * g x * c₁) * c₁⁻¹ := by group
    _ = c₁ * (u * x * u⁻¹) * c₁⁻¹ := by rw [this]
    _ = c₁ * u * x * (c₁ * u)⁻¹ := by group

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut
