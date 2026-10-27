module

public import CFSG.Quasithin.Vol2.Ch3E213MP2B
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.Blueprint

variable {A : Type*} [Group A] {K₁ K₂ : Subgroup A}

theorem exists_prime_orderOf_mem_normalizer {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    {n : ℕ} (hD : H13.QRC.BenderData G U n) (hn : 2 ≤ n) :
    ∃ h ∈ normalizer (U : Set G), ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf h = p := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpd)
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (normalizer (U : Set G)) := by
    rw [← hD.relIndex] at hpd
    exact hpd.trans (relIndex_dvd_card _ _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, x.2, p, hp, hp2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem pCore_le_sup [Finite A] {a : ℕ} {k : Type} [Field k]
    (ha : 1 ≤ a) (hk : Nat.card k = 2 ^ (2 * a + 1)) (θ₁ : K₁ ≃* suzukiGroup a k)
    (θ₂ : K₂ ≃* suzukiGroup a k) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ x : A, (∀ y ∈ K₁ ⊔ K₂, x * y = y * x) → x = 1) {B : Subgroup A} {h : A}
    (hhB : h ∈ B) (hhK : h ∈ K₁) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hhp : orderOf h = p) :
    inSubgroup (CFSG.pCore 2) B ≤ K₁ ⊔ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : IsSimpleGroup (suzukiGroup a k) := (CFSG.LieType.Ree.suzuki_simple ha hk).2.2
  have : IsSimpleGroup K₁ := θ₁.isSimpleGroup
  have : IsSimpleGroup K₂ := θ₂.isSimpleGroup
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hCK' : ∀ x : A, (∀ y ∈ K₂ ⊔ K₁, x * y = y * x) → x = 1 := fun x hx =>
    hCK x fun y hy => hx y (by rwa [sup_comm])
  have hZ₁ : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1 := fun z hz hzc =>
    eq_one_of_commute_sup hc' hCK' hz hzc
  have hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1 := fun z hz hzc =>
    eq_one_of_commute_sup hc hCK hz hzc
  have hcard : Nat.card K₁ = Nat.card K₂ :=
    (Nat.card_congr θ₁.toEquiv).trans (Nat.card_congr θ₂.toEquiv).symm
  have hK₁ : K₁ ≠ ⊥ := by
    intro h0
    have h1 : Nat.card K₁ = 1 := by rw [h0, card_bot]
    rw [Nat.card_congr θ₁.toEquiv] at h1
    exact (Finite.one_lt_card_iff_nontrivial.2
      (CFSG.LieType.Ree.suzuki_simple ha hk).2.1).ne' h1
  set R := inSubgroup (CFSG.pCore 2) B with hRdef
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup (p := 2) (G := B)).map _
  have hRn : B ≤ normalizer (R : Set A) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic B (CFSG.pCore 2 B))
  have hR₁ : R ≤ normalizer (K₁ : Set A) := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq]
    rcases H13.QRC.conj_factor_eq_or hc hn hZ₁ hcard r with h1 | h1
    · exact h1
    · exfalso
      have hcR : r * h * r⁻¹ * h⁻¹ ∈ R := by
        rw [show r * h * r⁻¹ * h⁻¹ = r * (h * r⁻¹ * h⁻¹) by group]
        exact R.mul_mem hr ((mem_normalizer_iff.1 (hRn hhB) r⁻¹).1 (R.inv_mem hr))
      obtain ⟨j, hj⟩ := hR2 ⟨_, hcR⟩
      have hj' : (r * h * r⁻¹ * h⁻¹) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h2 := pow_eq_one_of_swap hc hd h1 hhK hj'
      have h3 : p ∣ 2 ^ j := hhp ▸ orderOf_dvd_of_pow_eq_one h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hR₂ : R ≤ normalizer (K₂ : Set A) := fun r hr => by
    rw [mem_normalizer_iff_map_conj_eq]
    exact map_conj_eq_right hc hd hn hZ₂ hcard.symm hK₁
      ((mem_normalizer_iff_map_conj_eq).1 (hR₁ hr))
  exact le_sup_of_isPGroup ha hk θ₁ θ₂ hc hCK hR2 hR₁ hR₂

theorem map_conj_eq_left_of_swap [Finite A] (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hn : (K₁ ⊔ K₂).Normal) [IsSimpleGroup K₂]
    (hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1) (hcard : Nat.card K₂ = Nat.card K₁)
    (hK₂ : K₂ ≠ ⊥) {s : A} (hs : K₁.map (MulAut.conj s).toMonoidHom = K₂) :
    K₂.map (MulAut.conj s).toMonoidHom = K₁ := by
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hn' : (K₂ ⊔ K₁).Normal := by rwa [sup_comm]
  rcases H13.QRC.conj_factor_eq_or hc' hn' hZ₂ hcard s with h | h
  · exfalso
    apply hK₂
    have h1 : K₁ = K₂ := map_injective (MulAut.conj s).injective (hs.trans h.symm)
    rw [← hd, h1, inf_idem]
  · exact h

theorem isElementaryAbelian_proj (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
    {E : Subgroup A} [IsElementaryAbelian 2 E] (hEK : E ≤ K₁ ⊔ K₂) :
    IsElementaryAbelian 2 ((E ⊔ K₂) ⊓ K₁ : Subgroup A) := by
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian e he
  have hE : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨e, he⟩ ⟨f, hf⟩)
  have hK : ∀ {x : A}, x ∈ K₁ ⊓ K₂ → x = 1 := fun hx => by rwa [hd, mem_bot] at hx
  refine H13.QRC.isElementaryAbelian_of_le le_rfl (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨u₂, hu₂, hue⟩ := H13.QRC.exists_mul_mem_of_mem_proj hc hEK hu
    obtain ⟨v₂, hv₂, hve⟩ := H13.QRC.exists_mul_mem_of_mem_proj hc hEK hv
    have hcu : u₂ * v = v * u₂ := (hc v hv.2 u₂ hu₂.2).symm
    have hcv : v₂ * u = u * v₂ := (hc u hu.2 v₂ hv₂.2).symm
    have h1 : u * v * (u₂ * v₂) = v * u * (v₂ * u₂) :=
      calc u * v * (u₂ * v₂) = u * (v * u₂) * v₂ := by group
        _ = u * (u₂ * v) * v₂ := by rw [hcu]
        _ = u * u₂ * (v * v₂) := by group
        _ = v * v₂ * (u * u₂) := hE _ hue _ hve
        _ = v * (v₂ * u) * u₂ := by group
        _ = v * (u * v₂) * u₂ := by rw [hcv]
        _ = v * u * (v₂ * u₂) := by group
    have h2 : (v * u)⁻¹ * (u * v) = v₂ * u₂ * (u₂ * v₂)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
    have h3 : (v * u)⁻¹ * (u * v) ∈ K₁ ⊓ K₂ :=
      ⟨K₁.mul_mem (K₁.inv_mem (K₁.mul_mem hv.2 hu.2)) (K₁.mul_mem hu.2 hv.2), h2 ▸
        K₂.mul_mem (K₂.mul_mem hv₂.2 hu₂.2) (K₂.inv_mem (K₂.mul_mem hu₂.2 hv₂.2))⟩
    have h4 := hK h3
    rw [inv_mul_eq_one] at h4
    exact h4.symm
  · obtain ⟨u₂, hu₂, hue⟩ := H13.QRC.exists_mul_mem_of_mem_proj hc hEK hu
    have hcu : u₂ * u = u * u₂ := (hc u hu.2 u₂ hu₂.2).symm
    have h1 : u * u * (u₂ * u₂) = 1 :=
      calc u * u * (u₂ * u₂) = u * (u * u₂) * u₂ := by group
        _ = u * (u₂ * u) * u₂ := by rw [hcu]
        _ = u * u₂ * (u * u₂) := by group
        _ = 1 := hsq _ hue
    have h2 : u * u = (u₂ * u₂)⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hK ⟨K₁.mul_mem hu.2 hu.2, h2 ▸ K₂.inv_mem (K₂.mul_mem hu₂.2 hu₂.2)⟩

end CFSG.Quasithin.Ch3E213M.P2
