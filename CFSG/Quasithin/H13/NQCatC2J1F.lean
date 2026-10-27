module

public import CFSG.Quasithin.H13.NQCatC2J1

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.Walter.J1 CFSG.QuasithinUnique

variable {A : Type} [Group A] [Finite A] {Q₁ Q₂ : Subgroup A}

theorem le_of_exponent_three {Q : Subgroup A} (hJ : JankoHyp ↥Q) {C X : Subgroup A} (hCQ : C ≤ Q)
    (hXQ : X ≤ Q) (hC3 : ∀ c ∈ C, c ^ 3 = 1) (hX3 : Nat.card X = 3)
    (hXC : X ≤ Subgroup.normalizer (C : Set A)) : C ≤ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : IsPGroup 3 ↥C := IsPGroup.iff_orderOf.mpr fun c => by
    have h1 : orderOf c ∣ 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one (hC3 c c.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h' | h'
    · exact ⟨0, by rw [h', pow_zero]⟩
    · exact ⟨1, by rw [h', pow_one]⟩
  have hX : IsPGroup 3 ↥X := IsPGroup.of_card (n := 1) (by rw [hX3, pow_one])
  have hd := card_dvd_three_of_isPGroup hJ (sup_le hCQ hXQ) (hC.to_sup_of_normal_left' hX hXC)
  have heq : X = C ⊔ X := Subgroup.eq_of_le_of_card_ge le_sup_right
    (by rw [hX3]; exact Nat.le_of_dvd (by norm_num) hd)
  exact le_sup_left.trans heq.symm.le

theorem j1_img_le (h : CommPair Q₁ Q₂) (hJ₁ : JankoHyp ↥Q₁) (hJ₂ : JankoHyp ↥Q₂)
    {T D₀ B : Subgroup A} {s : A}
    (hsw₁ : ∀ z ∈ Q₁, s * z * s⁻¹ ∈ Q₂) (hsw₂ : ∀ z ∈ Q₂, s * z * s⁻¹ ∈ Q₁)
    (hT : IsSylowTwoOf T (Q₁ ⊔ Q₂)) (hD₀Q : D₀ ≤ Q₁ ⊔ Q₂) (hD₀c : IsCyclic ↥D₀)
    (hD₀o : Odd (Nat.card D₀))
    (hperm : ∀ t ∈ T, ∀ x ∈ D₀, ∃ x' ∈ D₀, ∃ t' ∈ T, t * x = x' * t')
    (hsD : ∀ x ∈ D₀, ∃ x' ∈ D₀, ∃ t ∈ T, s * x * s⁻¹ = x' * t)
    (hBQ : B ≤ Q₁ ⊔ Q₂) (hBD : B ≤ Subgroup.normalizer (D₀ : Set A)) (hB9 : Nat.card B = 9)
    (hB₁ : Nat.card (h.img₁ B) = 3) (hB₂ : Nat.card (h.img₂ B) = 3) :
    h.img₁ D₀ ≤ h.img₁ B ∧ h.img₂ D₀ ≤ h.img₂ B := by
  have hTQ := hT.1
  have hT₁ : IsSylowTwoOf (T ⊓ Q₁) Q₁ := h.isSylowTwoOf_inf₁ le_rfl le_rfl hT
  have hT₂ : IsSylowTwoOf (T ⊓ Q₂) Q₂ := h.isSylowTwoOf_inf₂ le_rfl le_rfl hT
  have hiT₁ : h.img₁ T = T ⊓ Q₁ := h.img₁_eq_of_sylow le_rfl le_rfl hT
  have hiT₂ : h.img₂ T = T ⊓ Q₂ := h.img₂_eq_of_sylow le_rfl le_rfl hT
  have hC₁o : Odd (Nat.card (h.img₁ D₀)) := Odd.of_dvd_nat hD₀o (h.card_img₁_dvd hD₀Q)
  have hC₂o : Odd (Nat.card (h.img₂ D₀)) := Odd.of_dvd_nat hD₀o (h.card_img₂_dvd hD₀Q)
  have hN₁ : h.img₁ D₀ ≤ Subgroup.normalizer ((T ⊓ Q₁ : Subgroup A) : Set A) :=
    le_normalizer_of_perm hJ₁ hT₁ (h.img₁_le D₀) (h.isCyclic_img₁ hD₀Q hD₀c) hC₁o
      (h.perm_img₁ hTQ hD₀Q (hiT₁ ▸ inf_le_left) hperm)
  have hN₂ : h.img₂ D₀ ≤ Subgroup.normalizer ((T ⊓ Q₂ : Subgroup A) : Set A) :=
    le_normalizer_of_perm hJ₂ hT₂ (h.img₂_le D₀) (h.isCyclic_img₂ hD₀Q hD₀c) hC₂o
      (h.perm_img₂ hTQ hD₀Q (hiT₂ ▸ inf_le_left) hperm)
  obtain ⟨g, hg⟩ := hD₀c.exists_generator
  obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := h.exists_mul_img hD₀Q g.2
  have hx₁Q := h.img₁_le D₀ hx₁
  have hx₂Q := h.img₂_le D₀ hx₂
  have hcx : Commute x₁ x₂ := h.comm x₁ hx₁Q x₂ hx₂Q
  have hdec : ∀ d ∈ D₀, ∃ j : ℤ, d = x₁ ^ j * x₂ ^ j := by
    intro d hd
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨d, hd⟩)
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow, hx, hcx.mul_zpow] at this
    exact this.symm
  have hproj : ∀ {a b : A}, a ∈ Q₁ → b ∈ Q₂ → a * b ∈ D₀ → ∃ j : ℤ, a = x₁ ^ j ∧ b = x₂ ^ j := by
    intro a b ha hb hab
    obtain ⟨j, hj⟩ := hdec _ hab
    exact ⟨j, h.eq_of_mul_eq_mul ha (zpow_mem hx₁Q j) hb (zpow_mem hx₂Q j) hj⟩
  have hor₁ := orderOf_of_mem_normalizer hJ₁ hT₁ hx₁Q (hN₁ hx₁)
    (Odd.of_dvd_nat hC₁o (Subgroup.orderOf_dvd_natCard _ hx₁))
  have hor₂ := orderOf_of_mem_normalizer hJ₂ hT₂ hx₂Q (hN₂ hx₂)
    (Odd.of_dvd_nat hC₂o (Subgroup.orderOf_dvd_natCard _ hx₂))
  have hcube : ∀ {y : A}, (orderOf y = 1 ∨ orderOf y = 3 ∨ orderOf y = 7) → orderOf y ≠ 7 →
      y ^ 3 = 1 := by
    intro y hy h7
    rcases hy with h' | h' | h'
    · rw [orderOf_eq_one_iff.mp h', one_pow]
    · rw [← h', pow_orderOf_eq_one]
    · exact absurd h' h7
  have hzc : ∀ {y : A} {j : ℤ}, y ^ 3 = 1 → (y ^ j) ^ 3 = 1 := by
    intro y j hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hBeq : B = h.img₁ B ⊔ h.img₂ B := by
    have hle : B ≤ h.img₁ B ⊔ h.img₂ B := fun y hy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_img hBQ hy
      exact Subgroup.mul_mem_sup ha hb
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [(h.mono (h.img₁_le B) (h.img₂_le B)).card_sup, hB₁, hB₂, hB9]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(h.img₁ B)) 3 (by rw [hB₁])
  have hB1le : h.img₁ B ≤ B :=
    calc h.img₁ B ≤ h.img₁ B ⊔ h.img₂ B := le_sup_left
      _ = B := hBeq.symm
  have hbB : (b : A) ∈ B := hB1le b.2
  have hbQ : (b : A) ∈ Q₁ := h.img₁_le B b.2
  have hbo : orderOf (b : A) = 3 := by rw [Subgroup.orderOf_coe, hb3]
  have hx7 : orderOf x₁ ≠ 7 ∧ orderOf x₂ ≠ 7 := by
    by_contra hcon
    rw [not_and_or, not_not, not_not] at hcon
    have hz : x₁ ^ 3 * x₂ ^ 3 ∈ D₀ := by
      have : (g : A) ^ 3 ∈ D₀ := pow_mem g.2 3
      rwa [hx, hcx.mul_pow] at this
    by_cases hb7 : orderOf x₁ = 7 ∧ orderOf x₂ = 7
    · obtain ⟨hA, hB'⟩ := hb7
      have hbx : (b : A) * (x₁ * x₂) * (b : A)⁻¹ ∈ D₀ := by
        rw [← hx]
        exact (Subgroup.mem_normalizer_iff.mp (hBD hbB) _).mp g.2
      have e : (b : A) * (x₁ * x₂) * (b : A)⁻¹ = ((b : A) * x₁ * (b : A)⁻¹) * x₂ := by
        have h1 : (b : A)⁻¹ * x₂ = x₂ * (b : A)⁻¹ := h.comm _ (inv_mem hbQ) x₂ hx₂Q
        calc (b : A) * (x₁ * x₂) * (b : A)⁻¹ = (b : A) * x₁ * (x₂ * (b : A)⁻¹) := by group
          _ = (b : A) * x₁ * ((b : A)⁻¹ * x₂) := by rw [h1]
          _ = ((b : A) * x₁ * (b : A)⁻¹) * x₂ := by group
      rw [e] at hbx
      obtain ⟨j, hj1, hj2⟩ := hproj (mul_mem (mul_mem hbQ hx₁Q) (inv_mem hbQ)) hx₂Q hbx
      have h1 : x₂ ^ (j - 1) = 1 := by rw [zpow_sub_one, ← hj2, mul_inv_cancel]
      have h2 : ((orderOf x₂ : ℕ) : ℤ) ∣ j - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hB'] at h2
      have h3 : x₁ ^ (j - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hA]; exact h2)
      have h4 : x₁ ^ j = x₁ := by
        rw [zpow_sub_one, mul_inv_eq_one] at h3
        exact h3
      rw [h4] at hj1
      apply false_of_seven_three hJ₁ hx₁Q hbQ hA hbo
      calc x₁ * (b : A) = ((b : A) * x₁ * (b : A)⁻¹) * b := by rw [hj1]
        _ = b * x₁ := by group
    · rcases hcon with hA | hB'
      ·
        have hx₂3 : x₂ ^ 3 = 1 := hcube hor₂ fun h' => hb7 ⟨hA, h'⟩
        rw [hx₂3, mul_one] at hz
        obtain ⟨x', hx', t, ht, hst⟩ := hsD _ hz
        obtain ⟨j, hj⟩ := hdec x' hx'
        obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h.exists_mul_img hTQ ht
        rw [hiT₁] at hc₁
        rw [hiT₂] at hc₂
        have hw : s * x₁ ^ 3 * s⁻¹ ∈ Q₂ := hsw₁ _ (pow_mem hx₁Q 3)
        have e : 1 * (s * x₁ ^ 3 * s⁻¹) = (x₁ ^ j * c₁) * (x₂ ^ j * c₂) := by
          rw [one_mul, hst, hj]
          have h1 : x₂ ^ j * c₁ = c₁ * x₂ ^ j :=
            (h.comm c₁ (Subgroup.mem_inf.mp hc₁).2 _ (zpow_mem hx₂Q j)).symm
          calc x₁ ^ j * x₂ ^ j * (c₁ * c₂) = x₁ ^ j * (x₂ ^ j * c₁) * c₂ := by group
            _ = x₁ ^ j * (c₁ * x₂ ^ j) * c₂ := by rw [h1]
            _ = x₁ ^ j * c₁ * (x₂ ^ j * c₂) := by group
        have hd := h.eq_of_mul_eq_mul (one_mem Q₁)
          (mul_mem (zpow_mem hx₁Q j) (Subgroup.mem_inf.mp hc₁).2) hw
          (mul_mem (zpow_mem hx₂Q j) (Subgroup.mem_inf.mp hc₂).2) e
        have hwo : orderOf (x₂ ^ j * c₂) = 7 := by
          rw [← hd.2, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
            Nat.Coprime.orderOf_pow (by rw [hA]; norm_num), hA]
        exact false_of_cube_mul hT₂.2.1 (zpow_mem (hN₂ hx₂) j) (hzc hx₂3) hc₂ hwo
      ·
        have hx₁3 : x₁ ^ 3 = 1 := hcube hor₁ fun h' => hb7 ⟨h', hB'⟩
        rw [hx₁3, one_mul] at hz
        obtain ⟨x', hx', t, ht, hst⟩ := hsD _ hz
        obtain ⟨j, hj⟩ := hdec x' hx'
        obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h.exists_mul_img hTQ ht
        rw [hiT₁] at hc₁
        rw [hiT₂] at hc₂
        have hw : s * x₂ ^ 3 * s⁻¹ ∈ Q₁ := hsw₂ _ (pow_mem hx₂Q 3)
        have e : (s * x₂ ^ 3 * s⁻¹) * 1 = (x₁ ^ j * c₁) * (x₂ ^ j * c₂) := by
          rw [mul_one, hst, hj]
          have h1 : x₂ ^ j * c₁ = c₁ * x₂ ^ j :=
            (h.comm c₁ (Subgroup.mem_inf.mp hc₁).2 _ (zpow_mem hx₂Q j)).symm
          calc x₁ ^ j * x₂ ^ j * (c₁ * c₂) = x₁ ^ j * (x₂ ^ j * c₁) * c₂ := by group
            _ = x₁ ^ j * (c₁ * x₂ ^ j) * c₂ := by rw [h1]
            _ = x₁ ^ j * c₁ * (x₂ ^ j * c₂) := by group
        have hd := h.eq_of_mul_eq_mul hw
          (mul_mem (zpow_mem hx₁Q j) (Subgroup.mem_inf.mp hc₁).2) (one_mem Q₂)
          (mul_mem (zpow_mem hx₂Q j) (Subgroup.mem_inf.mp hc₂).2) e
        have hwo : orderOf (x₁ ^ j * c₁) = 7 := by
          rw [← hd.1, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
            Nat.Coprime.orderOf_pow (by rw [hB']; norm_num), hB']
        exact false_of_cube_mul hT₁.2.1 (zpow_mem (hN₁ hx₁) j) (hzc hx₁3) hc₁ hwo
  have hx₁3 : x₁ ^ 3 = 1 := hcube hor₁ hx7.1
  have hx₂3 : x₂ ^ 3 = 1 := hcube hor₂ hx7.2
  refine ⟨le_of_exponent_three hJ₁ (h.img₁_le D₀) (h.img₁_le B) ?_ hB₁ ?_,
    le_of_exponent_three hJ₂ (h.img₂_le D₀) (h.img₂_le B) ?_ hB₂ ?_⟩
  · intro c hc
    obtain ⟨b', hb', hcb⟩ := h.exists_of_mem_img₁ hc
    obtain ⟨j, hj, -⟩ := hproj (h.img₁_le D₀ hc) hb' hcb
    rw [hj]
    exact hzc hx₁3
  · intro a ha
    obtain ⟨b', hb', hab⟩ := h.exists_of_mem_img₁ ha
    exact h.mem_normalizer_img₁ (h.img₁_le B ha) hb' (hBD hab)
  · intro c hc
    obtain ⟨a, ha, hac⟩ := h.exists_of_mem_img₂ hc
    obtain ⟨j, -, hj⟩ := hproj ha (h.img₂_le D₀ hc) hac
    rw [hj]
    exact hzc hx₂3
  · intro b' hb'
    obtain ⟨a, ha, hab⟩ := h.exists_of_mem_img₂ hb'
    exact h.mem_normalizer_img₂ ha (h.img₂_le B hb') (hBD hab)

end CFSG.Quasithin.H13.NQCat.C2
