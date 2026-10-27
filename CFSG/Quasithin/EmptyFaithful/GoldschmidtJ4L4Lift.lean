module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.J4L4

variable {M Q : Type*} [Group M] [Group Q]

theorem exists_odd_lift [Finite M] (π : M →* Q) (hπ : Function.Surjective π) {x : Q}
    (hx : Odd (orderOf x)) : ∃ y : M, Odd (orderOf y) ∧ π y = x := by
  obtain ⟨y₀, rfl⟩ := hπ x
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (π y₀)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hx)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(y₀ ^ (2 ^ a)) ^ k, ?_, ?_⟩
  · have h1 : ((y₀ ^ (2 ^ a)) ^ k) ^ m = 1 := by
      have : ((y₀ ^ (2 ^ a)) ^ k) ^ m = (y₀ ^ (2 ^ a * m)) ^ k := by
        rw [← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [this, ← hord, pow_orderOf_eq_one, one_pow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_pow, map_pow]
    exact hk

theorem eq_one_of_mem_ker_of_pow_five [Finite M] (π : M →* Q) (hP : IsPGroup 2 π.ker) {x : M}
    (hx : x ∈ π.ker) (h5 : x ^ 5 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have e2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h5)
    (orderOf_dvd_of_pow_eq_one e2))

theorem card_le_five_of_isPGroup [Finite M] [Finite Q] (π : M →* Q) (hP : IsPGroup 2 π.ker) {g : M}
    (hg : orderOf g = 5) {T : Subgroup M} (hT : T ≤ π.ker ⊔ Subgroup.zpowers g)
    (h5 : IsPGroup 5 T) : Nat.card T ≤ 5 := by
  have h5' : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hinj : Function.Injective (π.comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : M) ∈ π.ker := hx
    obtain ⟨k₁, hk₁⟩ := h5 x
    obtain ⟨k₂, hk₂⟩ := hP ⟨(x : M), hxk⟩
    have e1 : (x : M) ^ 5 ^ k₁ = 1 := by simpa using congrArg Subtype.val hk₁
    have e2 : (x : M) ^ 2 ^ k₂ = 1 := by simpa using congrArg Subtype.val hk₂
    have hc : Nat.Coprime (5 ^ k₁) (2 ^ k₂) := Nat.Coprime.pow _ _ (by norm_num)
    have : (x : M) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one e1
      have h2 := orderOf_dvd_of_pow_eq_one e2
      have := Nat.eq_one_of_dvd_coprimes hc h1 h2
      exact orderOf_eq_one_iff.1 this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hHle : π.ker ⊔ Subgroup.zpowers g ≤ (Subgroup.zpowers (π g)).comap π := by
    refine sup_le (fun k hk => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
      exact Subgroup.one_mem _
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [Subgroup.mem_comap, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
  have hrange : (π.comp T.subtype).range ≤ Subgroup.zpowers (π g) := by
    rintro _ ⟨t, rfl⟩
    exact hHle (hT t.2)
  have hz : Nat.card (Subgroup.zpowers (π g)) ≤ 5 := by
    rw [Nat.card_zpowers]
    refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have h1 := Subgroup.card_le_of_le hrange
  have h2 : Nat.card (π.comp T.subtype).range = Nat.card T :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  omega

theorem exists_centralizer_lift [Finite M] [Finite Q] (π : M →* Q) (hπ : Function.Surjective π)
    (hP : IsPGroup 2 π.ker) {g : M} (hg : orderOf g = 5) {d : Q} (hd : d * π g = π g * d) :
    ∃ m : M, m * g = g * m ∧ π m = d := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨m₀, rfl⟩ := hπ d
  set H : Subgroup M := π.ker ⊔ Subgroup.zpowers g with hH
  set g' : M := m₀ * g * m₀⁻¹ with hg'
  have hπg' : π g' = π g := by
    rw [hg', map_mul, map_mul, map_inv]
    exact mul_inv_eq_iff_eq_mul.2 hd
  have hkerk : g⁻¹ * g' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπg', inv_mul_cancel]
  have hgH : g ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hg'H : g' ∈ H := by
    have : g' = g * (g⁻¹ * g') := by group
    rw [this]
    exact H.mul_mem hgH (Subgroup.mem_sup_left hkerk)
  have hg'5 : orderOf g' = 5 := by
    have := orderOf_injective (MulAut.conj m₀).toMonoidHom (MulAut.conj m₀).injective g
    rw [hg']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this, hg]
  have hsyl : ∀ y : M, y ∈ H → orderOf y = 5 → ∃ P : Sylow 5 ↥H,
      ∀ x : ↥H, (x : M) ∈ Subgroup.zpowers y ↔ x ∈ (P : Subgroup ↥H) := by
    intro y hyH hy5
    let Sy : Subgroup ↥H := (Subgroup.zpowers y).subgroupOf H
    have hle : Subgroup.zpowers y ≤ H := Subgroup.zpowers_le.2 hyH
    have hcy : Nat.card Sy = 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hy5]
    have hpy : IsPGroup 5 Sy := IsPGroup.of_card (n := 1) (by rw [hcy]; norm_num)
    obtain ⟨P, hSP⟩ := hpy.exists_le_sylow
    refine ⟨P, fun x => ⟨fun hx => hSP hx, fun hx => ?_⟩⟩
    have hPM : IsPGroup 5 ((P : Subgroup ↥H).map H.subtype) :=
      P.isPGroup'.of_surjective (H.subtype.subgroupMap _) (H.subtype.subgroupMap_surjective _)
    have hcard := card_le_five_of_isPGroup π hP hg
      (T := (P : Subgroup ↥H).map H.subtype)
      (by rintro _ ⟨z, _, rfl⟩; exact z.2) hPM
    have hc2 : Nat.card (P : Subgroup ↥H) ≤ 5 := by
      rwa [Subgroup.card_map_of_injective H.subtype_injective] at hcard
    have heq : Sy = (P : Subgroup ↥H) :=
      Subgroup.eq_of_le_of_card_ge hSP (by rw [hcy]; exact hc2)
    have hx' : x ∈ Sy := heq ▸ hx
    exact hx'
  obtain ⟨P₁, hP₁⟩ := hsyl g hgH hg
  obtain ⟨P₂, hP₂⟩ := hsyl g' hg'H hg'5
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥H P₂ P₁
  have hconj : h * ⟨g', hg'H⟩ * h⁻¹ ∈ (P₁ : Subgroup ↥H) := by
    have hx2 : (⟨g', hg'H⟩ : ↥H) ∈ (P₂ : Subgroup ↥H) :=
      (hP₂ ⟨g', hg'H⟩).1 (Subgroup.mem_zpowers g')
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hx2, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((hP₁ _).2 hconj)
  have hm1 : (h : M) * m₀ * g * ((h : M) * m₀)⁻¹ = g ^ k := by
    have : (h : M) * g' * (h : M)⁻¹ = g ^ k := by
      simpa using hk.symm
    rw [← this, hg']
    group
  have hπH : ∀ y : M, y ∈ H → ∃ j : ℤ, π y = π g ^ j := by
    intro y hy
    have hle : H ≤ (Subgroup.zpowers (π g)).comap π := by
      refine sup_le (fun k hk => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
        exact Subgroup.one_mem _
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [Subgroup.mem_comap, map_zpow]
        exact Subgroup.zpow_mem_zpowers _ _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hle hy)
    exact ⟨j, hj.symm⟩
  obtain ⟨j, hj⟩ := hπH (h : M) h.2
  have hcomm : π ((h : M) * m₀) * π g = π g * π ((h : M) * m₀) := by
    rw [map_mul, hj, mul_assoc, hd, ← mul_assoc, ← mul_assoc]
    congr 1
    exact (Commute.zpow_left (Commute.refl (π g)) j).eq
  have hgk : g ^ k = g := by
    have h1 : (π g) ^ k = π g := by
      have e := congrArg π hm1
      simp only [map_mul, map_inv, map_zpow] at e
      have hc : π (h : M) * π m₀ * π g * (π (h : M) * π m₀)⁻¹ = π g := by
        have := hcomm
        rw [map_mul] at this
        exact mul_inv_eq_iff_eq_mul.2 this
      rw [e] at hc
      exact hc
    have h2 : g ^ (k - 1) ∈ π.ker := by
      rw [MonoidHom.mem_ker, zpow_sub_one, map_mul, map_zpow, map_inv, h1, mul_inv_cancel]
    have h3 : (g ^ (k - 1)) ^ 5 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
        one_zpow]
    have h4 := eq_one_of_mem_ker_of_pow_five π hP h2 h3
    rw [zpow_sub_one] at h4
    exact mul_inv_eq_one.1 h4
  have hcg : (h : M) * m₀ * g = g * ((h : M) * m₀) := by
    have := hm1
    rw [hgk] at this
    exact (mul_inv_eq_iff_eq_mul.1 this)
  have hgc : g ^ (-j) * g = g * g ^ (-j) := (Commute.zpow_left (Commute.refl g) (-j)).eq
  refine ⟨g ^ (-j) * ((h : M) * m₀), ?_, ?_⟩
  · calc g ^ (-j) * ((h : M) * m₀) * g = g ^ (-j) * (((h : M) * m₀) * g) := by rw [mul_assoc]
      _ = g ^ (-j) * (g * ((h : M) * m₀)) := by rw [hcg]
      _ = (g ^ (-j) * g) * ((h : M) * m₀) := by rw [mul_assoc]
      _ = (g * g ^ (-j)) * ((h : M) * m₀) := by rw [hgc]
      _ = g * (g ^ (-j) * ((h : M) * m₀)) := by rw [mul_assoc]
  · rw [map_mul, map_mul, map_zpow, hj, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
      one_mul]

end CFSG.Quasithin.J4L4
