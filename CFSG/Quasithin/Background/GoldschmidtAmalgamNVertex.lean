module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.F6.GoldAmN

open Subgroup CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

instance instNormalPCore (p : ℕ) (G : Type*) [Group G] : (pCore p G).Normal := pCore_normal p

theorem perm3_exists_order_three_prod : ∀ a : Equiv.Perm (Fin 3), a ≠ 1 →
    ∃ b : Equiv.Perm (Fin 3), (a * (b * a * b⁻¹)) ^ 3 = 1 ∧ a * (b * a * b⁻¹) ≠ 1 := by
  decide +kernel

theorem perm3_inv_of_involution : ∀ a τ : Equiv.Perm (Fin 3), a ^ 3 = 1 → a ≠ 1 → τ ^ 2 = 1 →
    τ ≠ 1 → τ * a * τ⁻¹ = a⁻¹ := by
  decide +kernel

theorem perm3_eq_or_eq_inv : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
    b ≠ 1 → b = a ∨ b = a⁻¹ := by
  decide +kernel

theorem perm3_involution_not_mem_zpowers : ∀ a τ : Equiv.Perm (Fin 3), a ^ 3 = 1 → τ ^ 2 = 1 →
    τ ≠ 1 → τ ∉ Subgroup.zpowers a := by
  intro a τ ha hτ hne hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hne
  have h3 : (a ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [ha]
  calc a ^ k = (a ^ k) ^ 3 * ((a ^ k) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hτ]; simp

section Abstract

variable {H : Type*} [Group H]

theorem eq_of_map_eq_of_pow_three (π : H →* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 π.ker)
    {a y : H} (ha : a ^ 3 = 1) (hy : y ^ 3 = 1) (hcomm : ∀ q ∈ π.ker, a * q = q * a)
    (hπ : π a = π y) : a = y := by
  have hq : a⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπ]; simp
  have hc : Commute a (a⁻¹ * y) := hcomm _ hq
  have h3 : (a⁻¹ * y) ^ 3 = 1 := by
    have hy' : y = a * (a⁻¹ * y) := by group
    have : (a * (a⁻¹ * y)) ^ 3 = 1 := by rw [← hy']; exact hy
    rw [hc.mul_pow, ha, one_mul] at this
    exact this
  have h1 : a⁻¹ * y = 1 := eq_one_of_mem_of_pow_three hker hq h3
  calc a = a * (a⁻¹ * y) := by rw [h1, mul_one]
    _ = y := by group

theorem exists_elt_of_not_centralizer_le [Finite H] (π : H →* Equiv.Perm (Fin 3))
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hnc : ¬ Subgroup.centralizer (π.ker : Set H) ≤ π.ker) :
    ∃ x : H, orderOf x = 3 ∧ (∀ q ∈ π.ker, x * q = q * x) ∧
      ∀ t : H, t ∉ π.ker → t ^ 2 ∈ π.ker → t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcC, hcK⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
  have hcc : ∀ q ∈ π.ker, c * q = q * c := fun q hq =>
    ((Subgroup.mem_centralizer_iff.mp hcC) q hq).symm
  have hπc : π c ≠ 1 := fun h => hcK h
  obtain ⟨b, hb3, hb1⟩ := perm3_exists_order_three_prod (π c) hπc
  obtain ⟨g, rfl⟩ := hπ b
  set c₂ : H := c * (g * c * g⁻¹) with hc₂
  have hc₂comm : ∀ q ∈ π.ker, c₂ * q = q * c₂ := by
    intro q hq
    have hgq : g⁻¹ * q * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv]
      rw [MonoidHom.mem_ker] at hq
      rw [hq]; simp
    have h1 := hcc _ hgq
    have h2 : (g * c * g⁻¹) * q = q * (g * c * g⁻¹) := by
      calc (g * c * g⁻¹) * q = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by rw [h1]
        _ = q * (g * c * g⁻¹) := by group
    calc c₂ * q = c * ((g * c * g⁻¹) * q) := by rw [hc₂, mul_assoc]
      _ = c * (q * (g * c * g⁻¹)) := by rw [h2]
      _ = (c * q) * (g * c * g⁻¹) := (mul_assoc _ _ _).symm
      _ = (q * c) * (g * c * g⁻¹) := by rw [hcc q hq]
      _ = q * c₂ := by rw [hc₂, mul_assoc]
  have hπc₂ : π c₂ = π c * (π g * π c * (π g)⁻¹) := by simp [hc₂]
  have hord : orderOf (π c₂) = 3 := by
    rw [hπc₂]; exact orderOf_eq_prime hb3 hb1
  have hdvd : 3 ∣ orderOf c₂ := hord ▸ orderOf_map_dvd π c₂
  set x : H := c₂ ^ (orderOf c₂ / 3) with hx
  have hxord : orderOf x = 3 := orderOf_pow_orderOf_div (orderOf_pos c₂).ne' hdvd
  have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxcomm : ∀ q ∈ π.ker, x * q = q * x := fun q hq =>
    ((Commute.pow_left (hc₂comm q hq) (orderOf c₂ / 3)))
  have hπx3 : (π x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hπx1 : π x ≠ 1 := by
    intro h
    have hxK : x ∈ π.ker := h
    have := eq_one_of_mem_of_pow_three hker hxK hx3
    rw [this] at hxord
    simp at hxord
  refine ⟨x, hxord, hxcomm, ?_⟩
  intro t htK ht2
  have hπt1 : π t ≠ 1 := fun h => htK h
  have hπt2 : (π t) ^ 2 = 1 := by rw [← map_pow]; exact ht2
  have hinv := perm3_inv_of_involution (π x) (π t) hπx3 hπx1 hπt2 hπt1
  have hy3 : (t * x * t⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3]; simp
  have hcommi : ∀ q ∈ π.ker, x⁻¹ * q = q * x⁻¹ := fun q hq =>
    (Commute.inv_left (show Commute x q from hxcomm q hq))
  have hπy : π x⁻¹ = π (t * x * t⁻¹) := by
    rw [map_inv, map_mul, map_mul, map_inv, hinv]
  exact (eq_of_map_eq_of_pow_three π hker (by rw [inv_pow, hx3, inv_one]) hy3 hcommi hπy).symm

end Abstract

section Ambient

variable {D : Type*} [Group D]

theorem mem_pCoreOf_iff {H : Subgroup D} {x : D} (hx : x ∈ H) :
    x ∈ pCoreOf 2 H ↔ (⟨x, hx⟩ : H) ∈ pCore 2 ↥H := by
  unfold pCoreOf
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]; exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem exists_hom_perm_three (H : Subgroup D)
    (hq : Nonempty (↥H ⧸ pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) :
    ∃ π : ↥H →* Equiv.Perm (Fin 3), Function.Surjective π ∧ π.ker = pCore 2 ↥H := by
  obtain ⟨e⟩ := hq
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  rw [show (e.toMonoidHom (QuotientGroup.mk x)) = e (QuotientGroup.mk x) from rfl,
    MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem exists_order_three_centralizing [Finite D] (H : Subgroup D)
    (hq : Nonempty (↥H ⧸ pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) (hnc : ¬ CharTwo H) :
    ∃ x ∈ H, orderOf x = 3 ∧ (∀ q ∈ pCoreOf 2 H, x * q = q * x) ∧
      ∀ t ∈ H, t ∉ pCoreOf 2 H → t ^ 2 ∈ pCoreOf 2 H → t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker⟩ := exists_hom_perm_three H hq
  have hpg : IsPGroup 2 π.ker := by rw [hker]; exact pCore_isPGroup 2
  have hcent : ¬ Subgroup.centralizer (π.ker : Set ↥H) ≤ π.ker := by
    intro hle
    apply hnc
    rintro g ⟨hgH, hgC⟩
    have hgc : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.centralizer (π.ker : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkD : (k : D) ∈ pCoreOf 2 H := ⟨k, by rw [← hker]; exact hk, rfl⟩
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hgC) (k : D) hkD)
    have h2 := hle hgc
    rw [hker] at h2
    exact (mem_pCoreOf_iff hgH).mpr h2
  obtain ⟨x, hx3, hxc, hxinv⟩ := exists_elt_of_not_centralizer_le π hπ hpg hcent
  refine ⟨(x : D), x.2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hx3
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := hq
    exact congrArg Subtype.val (hxc k (by rw [hker]; exact hk))
  · intro t htH htK ht2
    have h1 : (⟨t, htH⟩ : ↥H) ∉ π.ker := fun h =>
      htK ((mem_pCoreOf_iff htH).mpr (by rw [← hker]; exact h))
    have h2 : (⟨t, htH⟩ : ↥H) ^ 2 ∈ π.ker := by
      rw [hker]
      exact (mem_pCoreOf_iff (H.pow_mem htH 2)).mp ht2
    exact congrArg Subtype.val (hxinv ⟨t, htH⟩ h1 h2)

theorem nonempty_mulEquiv_dihedral_vertex [Finite D] (H : Subgroup D)
    (hq : Nonempty (↥H ⧸ pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) {x y σ : D} (hxH : x ∈ H)
    (hyH : y ∈ pCoreOf 2 H) (hσH : σ ∈ H) (hx3 : orderOf x = 3) (hxy : x * y = y * x)
    (hσK : σ ∉ pCoreOf 2 H) (hσ2 : σ ^ 2 = 1) (hσx : σ * x * σ⁻¹ = x⁻¹)
    (hσy : σ * y * σ⁻¹ = y⁻¹) (hcard : Nat.card H = 6 * orderOf y) :
    Nonempty (↥H ≃* DihedralGroup (3 * orderOf y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker⟩ := exists_hom_perm_three H hq
  have hyH' : y ∈ H := pCoreOf_le 2 H hyH
  have hcop : (orderOf y).Coprime (orderOf x) := by
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨y, hyH⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hx3]
    exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left k (by norm_num))
  have hρ : orderOf (y * x) = 3 * orderOf y := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (show Commute y x from hxy.symm) hcop,
      hx3, mul_comm]
  have hrel : σ * (y * x) * σ⁻¹ = (y * x)⁻¹ := by
    calc σ * (y * x) * σ⁻¹ = (σ * y * σ⁻¹) * (σ * x * σ⁻¹) := by group
      _ = y⁻¹ * x⁻¹ := by rw [hσy, hσx]
      _ = (y * x)⁻¹ := by
        rw [mul_inv_rev]
        exact (show Commute y⁻¹ x⁻¹ from (Commute.inv_inv (show Commute y x from hxy.symm))).eq
  have hnot : σ ∉ Subgroup.zpowers (y * x) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    let σ' : ↥H := ⟨σ, hσH⟩
    let x' : ↥H := ⟨x, hxH⟩
    let y' : ↥H := ⟨y, hyH'⟩
    have hy'K : y' ∈ π.ker := by rw [hker]; exact (mem_pCoreOf_iff hyH').mp hyH
    have hσ'K : σ' ∉ π.ker := fun hh => hσK ((mem_pCoreOf_iff hσH).mpr (by rw [← hker]; exact hh))
    have hπy : π y' = 1 := hy'K
    have hσ'k : σ' = (y' * x') ^ k := Subtype.ext (by simpa using hk.symm)
    have hπσ : π σ' = (π x') ^ k := by rw [hσ'k, map_zpow, map_mul, hπy, one_mul]
    have hπx3 : (π x') ^ 3 = 1 := by
      rw [← map_pow]
      have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
      have : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3')
      rw [this, map_one]
    have hπσ2 : (π σ') ^ 2 = 1 := by
      rw [← map_pow]
      have : σ' ^ 2 = 1 := Subtype.ext hσ2
      rw [this, map_one]
    have hπσ1 : π σ' ≠ 1 := fun hh => hσ'K hh
    exact perm3_involution_not_mem_zpowers (π x') (π σ') hπx3 hπσ2 hπσ1
      (hπσ ▸ Subgroup.zpow_mem_zpowers (π x') k)
  exact nonempty_mulEquiv_dihedral_of_mem H (mul_mem hyH' hxH) hσH hρ hσ2 hrel hnot
    (by rw [hcard]; ring)

theorem conj_order_three_mem [Finite D] (H : Subgroup D)
    (hq : Nonempty (↥H ⧸ pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) {x g : D} (hxH : x ∈ H)
    (hgH : g ∈ H) (hx3 : orderOf x = 3) :
    x⁻¹ * (g * x * g⁻¹) ∈ pCoreOf 2 H ∨ x * (g * x * g⁻¹) ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker⟩ := exists_hom_perm_three H hq
  have hpg : IsPGroup 2 π.ker := by rw [hker]; exact pCore_isPGroup 2
  let x' : ↥H := ⟨x, hxH⟩
  let g' : ↥H := ⟨g, hgH⟩
  have hx'3 : orderOf x' = 3 := by rw [Subgroup.orderOf_mk, hx3]
  have hx'3' : x' ^ 3 = 1 := by rw [← hx'3]; exact pow_orderOf_eq_one x'
  have hy'3 : (g' * x' * g'⁻¹) ^ 3 = 1 := by rw [conj_pow, hx'3']; simp
  have hy'1 : g' * x' * g'⁻¹ ≠ 1 := by
    intro h1
    have : x' = 1 := by
      have := congrArg (fun z => g'⁻¹ * z * g') h1
      simpa [mul_assoc] using this
    rw [this] at hx'3
    simp at hx'3
  have hy'ord : orderOf (g' * x' * g'⁻¹) = 3 := orderOf_eq_prime hy'3 hy'1
  have hπx3 : (π x') ^ 3 = 1 := by rw [← map_pow, hx'3', map_one]
  have hπx1 : π x' ≠ 1 := fun hh => not_mem_of_isPGroup_two hpg hx'3 hh
  have hπy3 : (π (g' * x' * g'⁻¹)) ^ 3 = 1 := by rw [← map_pow, hy'3, map_one]
  have hπy1 : π (g' * x' * g'⁻¹) ≠ 1 := fun hh => not_mem_of_isPGroup_two hpg hy'ord hh
  have hmem : ∀ z : D, ∀ hz : z ∈ H, (⟨z, hz⟩ : ↥H) ∈ π.ker → z ∈ pCoreOf 2 H := fun z hz hk =>
    (mem_pCoreOf_iff hz).mpr (by rw [← hker]; exact hk)
  have hxH' : x⁻¹ * (g * x * g⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hxH) (H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH))
  have hxH'' : x * (g * x * g⁻¹) ∈ H :=
    H.mul_mem hxH (H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH))
  rcases perm3_eq_or_eq_inv (π x') (π (g' * x' * g'⁻¹)) hπx3 hπx1 hπy3 hπy1 with h1 | h1
  · left
    refine hmem _ hxH' ?_
    show π (x'⁻¹ * (g' * x' * g'⁻¹)) = 1
    rw [map_mul, map_inv, h1]
    simp
  · right
    refine hmem _ hxH'' ?_
    show π (x' * (g' * x' * g'⁻¹)) = 1
    rw [map_mul, h1]
    simp

end Ambient

end CFSG.Quasithin.F6.GoldAmN
