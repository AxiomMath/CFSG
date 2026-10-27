module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped IsMulCommutative

variable {G : Type*} [Group G]

private lemma w16g_zpow_eq_one_of_dvd {M : Type*} [Group M] {a : M} (ha : a ^ 3 = 1)
    {m : ℤ} (hm : (3 : ℤ) ∣ m) : a ^ m = 1 := by
  obtain ⟨q, rfl⟩ := hm
  rw [zpow_mul]
  have h3 : a ^ (3 : ℤ) = 1 := by simpa using ha
  rw [h3, one_zpow]

private lemma w16g_defect_cent_eq {M : Type*} [CommGroup M] (c : M →* M) {x0 h y : M} {k : ℤ}
    (hk : h * x0 ^ k = y) :
    c y * y⁻¹ = (c h * h⁻¹) * (c x0 * x0⁻¹) ^ k := by
  rw [← hk, map_mul, map_zpow, mul_inv_rev, ← inv_zpow]
  rw [show c h * (c x0) ^ k * ((x0⁻¹) ^ k * h⁻¹)
        = (c h * h⁻¹) * ((c x0) ^ k * (x0⁻¹) ^ k) from by ac_rfl]
  rw [← mul_zpow]

private lemma w16g_defect_inv_eq {M : Type*} [CommGroup M] (c : M →* M) {x0 h y : M} {k : ℤ}
    (hk : h * x0 ^ k = y) :
    c y * y = (c h * h) * (c x0 * x0) ^ k := by
  rw [← hk, map_mul, map_zpow]
  rw [show c h * (c x0) ^ k * (h * x0 ^ k)
        = (c h * h) * ((c x0) ^ k * x0 ^ k) from by ac_rfl]
  rw [← mul_zpow]

theorem w16g_inv_or_cent_of_relIndex_three {X H : Subgroup G} {s : G}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hHX : H ≤ X) (hidx : H.relIndex X = 3) (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) (hsH : ∀ x ∈ H, s * x * s⁻¹ ∈ H) :
    (∀ x ∈ X, s * x * s⁻¹ * x ∈ H) ∨ (∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ H) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsHiff : ∀ x ∈ X, s * x * s⁻¹ ∈ H → x ∈ H := by
    intro x hxX hxH
    have hmem : s * (s * x * s⁻¹) * s⁻¹ ∈ H := hsH (s * x * s⁻¹) hxH
    have heq : s * (s * x * s⁻¹) * s⁻¹ = x := by
      rw [hsinv]
      calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
        _ = x := by rw [hs2, one_mul, mul_one]
    rwa [heq] at hmem
  have hXnotle : ¬ X ≤ H := by
    intro h
    have h1 : H.relIndex X = 1 := Subgroup.relIndex_eq_one.mpr h
    omega
  obtain ⟨x₀, hx₀X, hx₀H⟩ : ∃ x ∈ X, x ∉ H := by
    have : ¬ (X : Set G) ⊆ H := hXnotle
    exact Set.not_subset.mp this
  have hx₀pow : x₀ ^ 3 = 1 := hX3 x₀ hx₀X
  haveI : IsMulCommutative X :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hXc a.1 a.2 b.1 b.2)
  let x0 : X := ⟨x₀, hx₀X⟩
  have hx0pow : x0 ^ 3 = 1 := by ext; simpa using hx₀pow
  let y0 : X := ⟨s * x₀ * s⁻¹, hsX x₀ hx₀X⟩
  have hXeq : X = H ⊔ Subgroup.zpowers x₀ := by
    refine le_antisymm ?_ (sup_le hHX (Subgroup.zpowers_le.mpr hx₀X))
    let K : Subgroup G := H ⊔ Subgroup.zpowers x₀
    have hHK : H ≤ K := le_sup_left
    have hKX : K ≤ X := sup_le hHX (Subgroup.zpowers_le.mpr hx₀X)
    have hrel : H.relIndex K * K.relIndex X = 3 := by
      rw [Subgroup.relIndex_mul_relIndex H K X hHK hKX, hidx]
    have hne : H.relIndex K ≠ 1 := by
      intro h1
      exact hx₀H (Subgroup.relIndex_eq_one.mp h1
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₀)))
    have hdvd : H.relIndex K ∣ 3 := ⟨K.relIndex X, hrel.symm⟩
    have hHK3 : H.relIndex K = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd (H.relIndex K) hdvd with h1 | h3
      · exact absurd h1 hne
      · exact h3
    have hK1 : K.relIndex X = 1 := by
      have h3 : 3 * K.relIndex X = 3 := by rw [hHK3] at hrel; exact hrel
      omega
    exact Subgroup.relIndex_eq_one.mp hK1
  have hsupX : H.subgroupOf X ⊔ Subgroup.zpowers x0 = ⊤ :=
    Subgroup.map_subtype_inj.mp (by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hHX, MonoidHom.map_zpowers,
        Subgroup.map_top, Subgroup.range_subtype]
      exact hXeq.symm)
  have hdecomp : ∀ y : X, ∃ a : X, (a : G) ∈ H ∧ ∃ k : ℤ, a * x0 ^ k = y := by
    intro y
    have hy : y ∈ H.subgroupOf X ⊔ Subgroup.zpowers x0 := by
      rw [hsupX]; exact Subgroup.mem_top y
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨a, ha, k, by rw [← hk] at hab; exact hab⟩
  let cX : X →* X :=
    { toFun := fun y => ⟨s * y.1 * s⁻¹, hsX y.1 y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hcx0 : cX x0 = y0 := Subtype.ext rfl
  obtain ⟨h0, hh0, k₀, hk0⟩ := hdecomp y0
  have hk0not : ¬ (3 : ℤ) ∣ k₀ := by
    intro hdvd
    have hx0k : x0 ^ k₀ = 1 := w16g_zpow_eq_one_of_dvd hx0pow hdvd
    have hy0eq : y0 = h0 := by rw [← hk0, hx0k, mul_one]
    have hy0H : s * x₀ * s⁻¹ ∈ H := by
      have hval : y0.1 = h0.1 := congrArg Subtype.val hy0eq
      have hmem : y0.1 ∈ H := by rw [hval]; exact hh0
      simpa [y0] using hmem
    exact hx₀H (hsHiff x₀ hx₀X hy0H)
  have hk0mod_ne : k₀ % 3 ≠ 0 := by
    intro h
    exact hk0not (Int.dvd_iff_emod_eq_zero.mpr h)
  have hmod_cases : k₀ % 3 = 1 ∨ k₀ % 3 = 2 := by
    have hge : 0 ≤ k₀ % 3 := Int.emod_nonneg k₀ (by decide)
    have hlt : k₀ % 3 < 3 := Int.emod_lt_of_pos k₀ (by decide)
    omega
  rcases hmod_cases with hk1 | hk2
  · have hdvd1 : (3 : ℤ) ∣ k₀ - 1 := by
      have hmod : (1 : ℤ) ≡ k₀ [ZMOD 3] := by
        show (1 : ℤ) % 3 = k₀ % 3
        rw [hk1]
        exact Int.emod_eq_of_lt (by decide) (by decide)
      exact Int.modEq_iff_dvd.mp hmod
    have hx0pow1 : x0 ^ (k₀ - 1) = 1 := w16g_zpow_eq_one_of_dvd hx0pow hdvd1
    have hcx0inv : cX x0 * x0⁻¹ = h0 := by
      rw [hcx0, ← hk0, mul_assoc, ← zpow_sub_one, hx0pow1, mul_one]
    refine Or.inr ?_
    intro x hxX
    let yX : X := ⟨x, hxX⟩
    obtain ⟨hX, hhX, k, hk⟩ := hdecomp yX
    have hmem1 : (cX hX * hX⁻¹ : X) ∈ H.subgroupOf X := by
      show ((cX hX).1 * (hX⁻¹).1 : G) ∈ H
      exact H.mul_mem (hsH hX.1 hhX) (H.inv_mem hhX)
    have hmem2 : (cX x0 * x0⁻¹ : X) ∈ H.subgroupOf X := by
      rw [hcx0inv]
      exact hh0
    have hmem : (cX yX * yX⁻¹ : X) ∈ H.subgroupOf X := by
      rw [w16g_defect_cent_eq cX hk]
      exact (H.subgroupOf X).mul_mem hmem1 ((H.subgroupOf X).zpow_mem hmem2 k)
    have hfinal : ((cX yX * yX⁻¹ : X) : G) ∈ H := hmem
    simpa [cX, yX] using hfinal
  · have hdvd2 : (3 : ℤ) ∣ k₀ + 1 := by
      have hmod : (2 : ℤ) ≡ k₀ [ZMOD 3] := by
        show (2 : ℤ) % 3 = k₀ % 3
        rw [hk2]
        exact Int.emod_eq_of_lt (by decide) (by decide)
      have h := Int.modEq_iff_dvd.mp hmod
      have h2 : k₀ - 2 + 3 = k₀ + 1 := by omega
      rw [← h2]
      exact dvd_add h (dvd_refl 3)
    have hx0pow2 : x0 ^ (k₀ + 1) = 1 := w16g_zpow_eq_one_of_dvd hx0pow hdvd2
    have hcx0mul : cX x0 * x0 = h0 := by
      rw [hcx0, ← hk0, mul_assoc, ← zpow_add_one, hx0pow2, mul_one]
    refine Or.inl ?_
    intro x hxX
    let yX : X := ⟨x, hxX⟩
    obtain ⟨hX, hhX, k, hk⟩ := hdecomp yX
    have hmem1 : (cX hX * hX : X) ∈ H.subgroupOf X := by
      show ((cX hX).1 * hX.1 : G) ∈ H
      exact H.mul_mem (hsH hX.1 hhX) hhX
    have hmem2 : (cX x0 * x0 : X) ∈ H.subgroupOf X := by
      rw [hcx0mul]
      exact hh0
    have hmem : (cX yX * yX : X) ∈ H.subgroupOf X := by
      rw [w16g_defect_inv_eq cX hk]
      exact (H.subgroupOf X).mul_mem hmem1 ((H.subgroupOf X).zpow_mem hmem2 k)
    have hfinal : ((cX yX * yX : X) : G) ∈ H := hmem
    simpa [cX, yX] using hfinal

theorem w16g_cent_of_fixed_outside {X H : Subgroup G} {s z : G}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hHX : H ≤ X) (hidx : H.relIndex X = 3) (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) (hsH : ∀ x ∈ H, s * x * s⁻¹ ∈ H)
    (hzX : z ∈ X) (hzH : z ∉ H) (hsz : s * z * s⁻¹ = z) :
    ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ H := by
  rcases w16g_inv_or_cent_of_relIndex_three hXc hX3 hHX hidx hs2 hsX hsH with h | h
  · exfalso
    have hz : z * z ∈ H := by
      have h1 := h z hzX
      rwa [hsz] at h1
    have hz4 : z ∈ H := by
      have h2 : (z * z) * (z * z) ∈ H := H.mul_mem hz hz
      have h3 : (z * z) * (z * z) = z := by
        have hz3 : z ^ 3 = 1 := hX3 z hzX
        calc (z * z) * (z * z) = z ^ 4 := by
              rw [← pow_two (z * z), (Commute.refl z).mul_pow 2, ← pow_add]
          _ = z := by rw [show (4 : ℕ) = 3 + 1 by omega, pow_add, hz3, one_mul, pow_one]
      rwa [h3] at h2
    exact hzH hz4
  · exact h

end CFSG.LocalAnalysis.WeakClosure81
