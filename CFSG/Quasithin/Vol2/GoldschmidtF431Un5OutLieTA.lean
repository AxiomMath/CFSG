module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

section Lift

variable {G Q : Type*} [Group G] [Group Q]

theorem un5ta_eq_one_of_two_elem {z : G} {k : ℕ} (hz : Odd (orderOf z)) (h : z ^ 2 ^ k = 1) :
    z = 1 := by
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : Nat.Coprime (orderOf z) 2 := Nat.coprime_two_right.mpr hz
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h2) h1)

theorem un5ta_exists_lift [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center G ∧ Odd (orderOf z))
    (σ : MulAut G) (τ : MulAut Q) (hστ : ∀ g, π (σ g) = τ (π g))
    (R : Subgroup Q) (hR : IsPGroup 2 R) (hfix : ∀ x ∈ R, τ x = x) :
    ∃ H : Subgroup G, IsPGroup 2 H ∧ (∀ h ∈ H, σ h = h) ∧ H.map π = R ∧
      ∀ a ∈ H, ∀ b ∈ H, π a = π b → a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' : Subgroup G := R.comap π with hR'
  obtain ⟨P⟩ : Nonempty (Sylow 2 R') := inferInstance
  set H : Subgroup G := (P : Subgroup R').map R'.subtype with hH
  have hH2 : IsPGroup 2 H := P.isPGroup'.map R'.subtype
  have hHR' : H ≤ R' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hHk : ∀ h ∈ H, ∃ k : ℕ, h ^ 2 ^ k = 1 := fun h hh => by
    obtain ⟨k, hk⟩ := hH2 ⟨h, hh⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hinj : ∀ a ∈ H, ∀ b ∈ H, π a = π b → a = b := by
    intro a ha b hb hab
    have hz : a⁻¹ * b ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hH2 ⟨a⁻¹ * b, H.mul_mem (H.inv_mem ha) hb⟩
    have := un5ta_eq_one_of_two_elem (hker _ hz).2 (congrArg Subtype.val hk)
    exact inv_mul_eq_one.1 this
  have hfixH : ∀ h ∈ H, σ h = h := by
    intro h hh
    have hπh : π h ∈ R := hHR' hh
    have hz : σ h * h⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hστ, hfix _ hπh, mul_inv_cancel]
    obtain ⟨k, hk⟩ := hHk h hh
    have hc : Commute (σ h * h⁻¹) h := ((Subgroup.mem_center_iff.1 (hker _ hz).1) h).symm
    have h1 : (σ h * h⁻¹) ^ 2 ^ k = 1 := by
      have e : σ h = (σ h * h⁻¹) * h := by group
      have e2 : (σ h) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
      have e3 : ((σ h * h⁻¹) * h) ^ 2 ^ k = (σ h * h⁻¹) ^ 2 ^ k * h ^ 2 ^ k := hc.mul_pow _
      rw [← e, e2, hk, mul_one] at e3
      exact e3.symm
    exact mul_inv_eq_one.1 (un5ta_eq_one_of_two_elem (hker _ hz).2 h1)
  refine ⟨H, hH2, hfixH, ?_, hinj⟩
  have hZR' : π.ker ≤ R' := fun z hz => by
    rw [hR', Subgroup.mem_comap, (MonoidHom.mem_ker).1 hz]
    exact R.one_mem
  let φ : R' →* R := (π.comp R'.subtype).codRestrict R (fun x => x.2)
  have hφs : Function.Surjective φ := by
    intro r
    obtain ⟨g, hg⟩ := hπ (r : Q)
    exact ⟨⟨g, by rw [hR', Subgroup.mem_comap, hg]; exact r.2⟩, Subtype.ext hg⟩
  have hker' : φ.ker = π.ker.subgroupOf R' := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.codRestrict, Subtype.ext_iff]
  have hcardR' : Nat.card R' = Nat.card π.ker * Nat.card R := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hφs, hker']
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR').toEquiv
  have hZodd : ¬ 2 ∣ Nat.card π.ker := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
    have := (hker _ x.2).2
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  have : Finite Q := Finite.of_surjective π hπ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
  have hHcard : Nat.card H = Nat.card R := by
    have h1 : Nat.card H = Nat.card (P : Subgroup R') :=
      Subgroup.card_map_of_injective R'.subtype_injective
    have hpos : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    rw [h1, P.card_eq_multiplicity, hcardR', hn, Nat.factorization_mul hpos (by positivity),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hZodd, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
    simp
  have hle : H.map π ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hHR' hx
  have hcard : Nat.card R ≤ Nat.card (H.map π) := by
    rw [← hHcard]
    exact Nat.card_le_card_of_injective
      (fun x : H => (⟨π x, Subgroup.mem_map_of_mem _ x.2⟩ : H.map π))
      (fun a b hab => Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)))
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end Lift

end CFSG.Quasithin.H13.F431.Un.OL5
