module

public import CFSG.RankThree.PartOne.S11c.HeisenbergSylow

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup

section Coverage

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_pow_of_orderOf_prime {p : ℕ} [Fact p.Prime] (hp : ¬ p ^ 2 ∣ Nat.card G)
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) :
    ∃ (g : G) (k : ℕ), g * y * g⁻¹ = x ^ k := by
  classical
  have hdvd : p ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
  have hfac : (Nat.card G).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card G).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 (by simpa using hdvd)
    have h2 : ¬ 2 ≤ (Nat.card G).factorization p := fun h =>
      hp ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').2 h)
    omega
  have hT : p ^ (Nat.card G).factorization p ∣ Nat.card (zpowers x) := by
    rw [hfac, Nat.card_zpowers, hx, pow_one]
  have hA : IsPGroup p (zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy, pow_one]
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_dvd_pow (zpowers x) hT hA
  have hmem : c * y * c⁻¹ ∈ zpowers x := hc y (mem_zpowers y)
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hmem
  obtain ⟨k, -, hk⟩ := hmem
  exact ⟨c, k, hk.symm⟩

theorem commute_of_commute_pow {p : ℕ} [Fact p.Prime] {u f : G} {k : ℕ} (hu : orderOf u = p)
    (hy : orderOf (u ^ k) = p) (h : f * u ^ k = u ^ k * f) : f * u = u * f := by
  have hle : zpowers (u ^ k) ≤ zpowers u := by
    rw [zpowers_le]
    exact pow_mem (mem_zpowers u) k
  have heq : zpowers (u ^ k) = zpowers u := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hu, hy]
  have hmem : u ∈ zpowers (u ^ k) := heq ▸ mem_zpowers u
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
  rw [← hm]
  exact (Commute.zpow_right (show Commute f (u ^ k) from h) m).eq

theorem exists_conj_pow_of_commute_seven {u₀ : G} (hu₀ : orderOf u₀ = 7)
    (h49 : ¬ 7 ^ 2 ∣ Nat.card G)
    (h25 : ¬ 5 ^ 2 ∣ Nat.card (centralizer ({u₀} : Set G))) {f w : G}
    (hf : orderOf f = 5) (hw : orderOf w = 5)
    (hfu : ∃ u : G, orderOf u = 7 ∧ f * u = u * f)
    (hwu : ∃ u : G, orderOf u = 7 ∧ w * u = u * w) :
    ∃ (g : G) (a : ℕ), w = g * f ^ a * g⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have red : ∀ z : G, orderOf z = 5 → (∃ u : G, orderOf u = 7 ∧ z * u = u * z) →
      ∃ g : G, g * z * g⁻¹ ∈ centralizer ({u₀} : Set G) := by
    rintro z hz ⟨u, hu, hzu⟩
    obtain ⟨g, k, hgk⟩ := exists_conj_pow_of_orderOf_prime (p := 7) h49 hu₀ hu
    refine ⟨g, ?_⟩
    have hyo : orderOf (u₀ ^ k) = 7 := by
      rw [← hgk]
      have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
      rw [← hu]
      exact h1
    have hc : g * z * g⁻¹ * u₀ ^ k = u₀ ^ k * (g * z * g⁻¹) := by
      rw [← hgk]
      calc g * z * g⁻¹ * (g * u * g⁻¹) = g * (z * u) * g⁻¹ := by group
        _ = g * (u * z) * g⁻¹ := by rw [hzu]
        _ = g * u * g⁻¹ * (g * z * g⁻¹) := by group
    rw [mem_centralizer_singleton_iff]
    exact commute_of_commute_pow hu₀ hyo hc
  obtain ⟨g₁, hg₁⟩ := red f hf hfu
  obtain ⟨g₂, hg₂⟩ := red w hw hwu
  have hconj : ∀ (z g : G), orderOf z = 5 → orderOf (g * z * g⁻¹) = 5 := fun z g hz => by
    rw [← hz]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
  let f₁ : centralizer ({u₀} : Set G) := ⟨g₁ * f * g₁⁻¹, hg₁⟩
  let w₂ : centralizer ({u₀} : Set G) := ⟨g₂ * w * g₂⁻¹, hg₂⟩
  have hf₁ : orderOf f₁ = 5 := by
    rw [← hconj f g₁ hf]
    exact Subgroup.orderOf_mk _ _
  have hw₂ : orderOf w₂ = 5 := by
    rw [← hconj w g₂ hw]
    exact Subgroup.orderOf_mk _ _
  obtain ⟨c, k, hck⟩ := exists_conj_pow_of_orderOf_prime (G := centralizer ({u₀} : Set G))
    (p := 5) h25 hf₁ hw₂
  have hck' : (c : G) * (g₂ * w * g₂⁻¹) * (c : G)⁻¹ = (g₁ * f * g₁⁻¹) ^ k :=
    congrArg Subtype.val hck
  rw [conj_pow] at hck'
  refine ⟨g₂⁻¹ * (c : G)⁻¹ * g₁, k, ?_⟩
  calc w = g₂⁻¹ * ((c : G)⁻¹ * ((c : G) * (g₂ * w * g₂⁻¹) * (c : G)⁻¹) * (c : G)) * g₂ := by
        group
    _ = g₂⁻¹ * ((c : G)⁻¹ * (g₁ * f ^ k * g₁⁻¹) * (c : G)) * g₂ := by rw [hck']
    _ = g₂⁻¹ * (c : G)⁻¹ * g₁ * f ^ k * (g₂⁻¹ * (c : G)⁻¹ * g₁)⁻¹ := by group

omit [Finite G] in
theorem card_centralizer_conj (x g : G) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv fun y => ?_)
  simp only [mem_centralizer_singleton_iff, MulAut.conj_apply, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv]
  constructor
  · intro h
    calc g⁻¹ * y * g⁻¹⁻¹ * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g⁻¹⁻¹) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

theorem centralizer_pow_eq {f : G} {a : ℕ} (hf : orderOf f = 5) (ha : orderOf (f ^ a) = 5) :
    centralizer ({f ^ a} : Set G) = centralizer ({f} : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzp : zpowers (f ^ a) = zpowers f := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [zpowers_le]
      exact pow_mem (mem_zpowers f) a
    · rw [Nat.card_zpowers, Nat.card_zpowers, hf, ha]
  ext y
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hmem : f ∈ zpowers (f ^ a) := hzp ▸ mem_zpowers f
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
    rw [← hm]
    exact (Commute.zpow_right (show Commute y (f ^ a) from h) m).eq
  · intro h
    exact (Commute.pow_right (show Commute y f from h) a).eq

theorem card_centralizer_eq_of_conj_pow {f w : G} (hf : orderOf f = 5) (hw : orderOf w = 5)
    {g : G} {a : ℕ} (h : w = g * f ^ a * g⁻¹) :
    Nat.card (centralizer ({w} : Set G)) = Nat.card (centralizer ({f} : Set G)) := by
  have hfa : orderOf (f ^ a) = 5 := by
    have h1 : orderOf (g * f ^ a * g⁻¹) = orderOf (f ^ a) :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (f ^ a)
    rw [← h, hw] at h1
    exact h1.symm
  rw [h, card_centralizer_conj, centralizer_pow_eq hf hfa]

end Coverage

end CFSG.RankThree.PartOne.HNRed
