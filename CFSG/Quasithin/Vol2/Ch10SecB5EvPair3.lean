module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvPairQ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {Kc S X P3 : Subgroup G} {Q₁ Q₂ : Type} [Group Q₁]
  [Group Q₂] [Finite Q₁] [Finite Q₂] {φ : ↥Kc →* Q₁ × Q₂}

omit [Finite G] in
theorem mem_of_mul_of_orderOf_three {x o : G} (hx : x ∈ X)
    (ho : o ∈ Subgroup.normalizer (X : Set G)) {j : ℕ} (hoj : o ^ 2 ^ j = 1)
    (h3 : orderOf (x * o) = 3) : x * o ∈ X := by
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hx ho (2 ^ j)
  rw [hoj, mul_one] at hpow
  have hcop : Nat.Coprime (2 ^ j) (orderOf (x * o)) := by
    rw [h3]
    exact Nat.Coprime.pow_left j (by norm_num)
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  rw [hpow] at hmem
  exact (Subgroup.zpowers_le.mpr hx') hmem

omit [Finite G] [Finite Q₁] [Finite Q₂] in
theorem pow_three_of_mem_map {Q : Type} [Group Q] (π : ↥Kc →* Q)
    (hP33 : ∀ x ∈ P3, x ^ 3 = 1) : ∀ a ∈ (P3.subgroupOf Kc).map π, a ^ 3 = 1 := by
  rintro _ ⟨p, hp, rfl⟩
  have : p ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hP33 _ hp)
  rw [← map_pow, this, map_one]

omit [Finite Q₁] [Finite Q₂] in
theorem card_map_P (hker : φ.ker = (pCoreOf 2 Kc).subgroupOf Kc) (hPK : P3 ≤ Kc)
    (hP33 : ∀ x ∈ P3, x ^ 3 = 1) : Nat.card ((P3.subgroupOf Kc).map φ) = Nat.card P3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := φ.comp (P3.subgroupOf Kc).subtype with hρ
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).mpr fun p hp => ?_
    have hk : ((p : ↥Kc)) ∈ φ.ker := hp
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have h1 := eq_one_of_pow_three_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) hk (hP33 _ p.2)
    exact Subtype.ext (Subtype.ext h1)
  rw [show (P3.subgroupOf Kc).map φ = ρ.range by
      rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype],
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]

theorem mem_of_orderOf_three_of_pair
    {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (he₁ : Even n₁) (he₂ : Even n₂)
    (hF₁ : Nat.card F₁ = 2 ^ n₁) (hF₂ : Nat.card F₂ = 2 ^ n₂)
    (e₁ : Q₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Q₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (hφ : Function.Surjective φ)
    (hker : φ.ker = (pCoreOf 2 Kc).subgroupOf Kc) (hS : IsSylowTwoOf S Kc) (hXK : X ≤ Kc)
    (h5 : ¬ 5 ∣ Nat.card ↥(X ⊔ S)) (hSX : S ≤ Subgroup.normalizer (X : Set G))
    (hP3X : P3 ≤ X) (hP3 : Nat.card P3 = 9) (hP33 : ∀ x ∈ P3, x ^ 3 = 1) {g : G}
    (hg : g ∈ Kc ⊓ Subgroup.normalizer (S : Set G)) (hg3 : orderOf g = 3) : g ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU₁, hU₂, hφS⟩ := map_sylow_eq_prod hφ hS
  have hXN := le_normalizer_of_pair hn₁ hn₂ he₁ he₂ hF₁ hF₂ e₁ e₂ hφ hker hS hXK h5
  have hO : pCoreOf 2 Kc ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS
  set π₁ := (MonoidHom.fst Q₁ Q₂).comp φ with hπ₁
  set π₂ := (MonoidHom.snd Q₁ Q₂).comp φ with hπ₂
  have hAN₁ : (P3.subgroupOf Kc).map π₁ ≤
      Subgroup.normalizer (((S.subgroupOf Kc).map π₁ : Subgroup Q₁) : Set Q₁) := by
    rintro _ ⟨p, hp, rfl⟩
    exact proj_mem_normalizer π₁ p.2 (hXN (hP3X hp))
  have hAN₂ : (P3.subgroupOf Kc).map π₂ ≤
      Subgroup.normalizer (((S.subgroupOf Kc).map π₂ : Subgroup Q₂) : Set Q₂) := by
    rintro _ ⟨p, hp, rfl⟩
    exact proj_mem_normalizer π₂ p.2 (hXN (hP3X hp))
  have hc₁ := card_le_three hF₁ e₁ hU₁ hAN₁ (pow_three_of_mem_map π₁ hP33)
  have hc₂ := card_le_three hF₂ e₂ hU₂ hAN₂ (pow_three_of_mem_map π₂ hP33)
  have hle : (P3.subgroupOf Kc).map φ ≤
      ((P3.subgroupOf Kc).map π₁).prod ((P3.subgroupOf Kc).map π₂) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hcP := card_map_P hker (hP3X.trans hXK) hP33
  have hcprod : Nat.card ↥(((P3.subgroupOf Kc).map π₁).prod ((P3.subgroupOf Kc).map π₂)) =
      Nat.card ((P3.subgroupOf Kc).map π₁) * Nat.card ((P3.subgroupOf Kc).map π₂) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have h9 := Subgroup.card_le_of_le hle
  rw [hcP, hP3, hcprod] at h9
  have hc₁3 : Nat.card ((P3.subgroupOf Kc).map π₁) = 3 := by nlinarith
  have hc₂3 : Nat.card ((P3.subgroupOf Kc).map π₂) = 3 := by nlinarith
  have hPeq : (P3.subgroupOf Kc).map φ =
      ((P3.subgroupOf Kc).map π₁).prod ((P3.subgroupOf Kc).map π₂) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcprod, hcP, hP3, hc₁3, hc₂3])
  have hgen : ∀ {Q : Type} [Group Q] (A : Subgroup Q), Nat.card A = 3 → (∀ a ∈ A, a ^ 3 = 1) →
      ∃ a ∈ A, orderOf a = 3 := by
    intro Q _ A hA hA3
    have hne : A ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hA; norm_num at hA
    obtain ⟨⟨a, haA⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
    refine ⟨a, haA, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one (hA3 a haA)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  obtain ⟨a₁, ha₁, ha₁3⟩ := hgen _ hc₁3 (pow_three_of_mem_map π₁ hP33)
  obtain ⟨a₂, ha₂, ha₂3⟩ := hgen _ hc₂3 (pow_three_of_mem_map π₂ hP33)
  have hPX : (P3.subgroupOf Kc).map φ ≤ (X.subgroupOf Kc).map φ :=
    Subgroup.map_mono fun p hp => hP3X hp
  have hA₁ : ((a₁, 1) : Q₁ × Q₂) ∈ (X.subgroupOf Kc).map φ :=
    hPX (by rw [hPeq]; exact ⟨ha₁, Subgroup.one_mem _⟩)
  have hA₂ : ((1, a₂) : Q₁ × Q₂) ∈ (X.subgroupOf Kc).map φ :=
    hPX (by rw [hPeq]; exact ⟨Subgroup.one_mem _, ha₂⟩)
  have hconj : ∀ q ∈ (S.subgroupOf Kc).map φ, ∀ y ∈ (X.subgroupOf Kc).map φ,
      q * y * q⁻¹ * y⁻¹ ∈ (X.subgroupOf Kc).map φ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨s * x * s⁻¹ * x⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have h1 : (s : G) * x * (s : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hSX hs) _).mp hx
    exact X.mul_mem h1 (X.inv_mem hx)
  have hU₁X : ∀ u ∈ (S.subgroupOf Kc).map π₁, ((u, 1) : Q₁ × Q₂) ∈ (X.subgroupOf Kc).map φ := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := exists_commutator_eq hF₁ e₁ hU₁ (hAN₁ ha₁) ha₁3 hu
    have hw' : ((w, 1) : Q₁ × Q₂) ∈ (S.subgroupOf Kc).map φ := by
      rw [hφS]; exact ⟨hw, Subgroup.one_mem _⟩
    have := hconj _ hw' _ hA₁
    simpa using this
  have hU₂X : ∀ u ∈ (S.subgroupOf Kc).map π₂, ((1, u) : Q₁ × Q₂) ∈ (X.subgroupOf Kc).map φ := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := exists_commutator_eq hF₂ e₂ hU₂ (hAN₂ ha₂) ha₂3 hu
    have hw' : ((1, w) : Q₁ × Q₂) ∈ (S.subgroupOf Kc).map φ := by
      rw [hφS]; exact ⟨Subgroup.one_mem _, hw⟩
    have := hconj _ hw' _ hA₂
    simpa using this
  set gk : ↥Kc := ⟨g, hg.1⟩ with hgk
  have hg3' : gk ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hgk, ← hg3]; exact pow_orderOf_eq_one g)
  obtain ⟨i₁, u₁, hu₁, h₁⟩ := exists_pow_mul_of_pow_three hF₁ e₁ hU₁ (hAN₁ ha₁) ha₁3
    (proj_mem_normalizer π₁ hg.1 hg.2) (by rw [← map_pow, hg3', map_one])
  obtain ⟨i₂, u₂, hu₂, h₂⟩ := exists_pow_mul_of_pow_three hF₂ e₂ hU₂ (hAN₂ ha₂) ha₂3
    (proj_mem_normalizer π₂ hg.1 hg.2) (by rw [← map_pow, hg3', map_one])
  have hφg : φ gk = ((a₁, 1) : Q₁ × Q₂) ^ i₁ * (u₁, 1) * (((1, a₂) : Q₁ × Q₂) ^ i₂ * (1, u₂)) := by
    refine Prod.ext ?_ ?_
    · have : (φ gk).1 = a₁ ^ i₁ * u₁ := h₁
      simp [this]
    · have : (φ gk).2 = a₂ ^ i₂ * u₂ := h₂
      simp [this]
  have hgX : φ gk ∈ (X.subgroupOf Kc).map φ := by
    rw [hφg]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hA₁ _) (hU₁X _ hu₁))
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hA₂ _) (hU₂X _ hu₂))
  obtain ⟨x, hx, hxg⟩ := hgX
  have hk : x⁻¹ * gk ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) ⟨_, hk⟩
  have hj' : (((x⁻¹ * gk : ↥Kc) : G)) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hgeq : (x : G) * ((x⁻¹ * gk : ↥Kc) : G) = g := by simp [hgk]
  have hx' : (x : G) ∈ X := hx
  have := mem_of_mul_of_orderOf_three (X := X) hx' (hSX (hO hk)) hj' (by rw [hgeq]; exact hg3)
  rwa [hgeq] at this

end CFSG.Quasithin.Vol2.Ch10.SecB
