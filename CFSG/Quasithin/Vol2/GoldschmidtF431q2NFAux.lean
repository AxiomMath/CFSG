module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2Syl

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_of_index_two {T Q : Subgroup G} (hle : Q ≤ T)
    (hcard : Nat.card T = 2 * Nat.card Q) : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup T := Q.subgroupOf T with hK
  have hKc : Nat.card K = Nat.card Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    have hpos : 0 < Nat.card Q := Nat.card_pos
    rw [hKc, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hidx
  have hQ : Nat.card (T ⧸ K) = 2 := hidx
  have hcyc : IsCyclic (T ⧸ K) := isCyclic_of_prime_card hQ
  intro x hx y hy
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk ⟨x, hx⟩))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk ⟨y, hy⟩))
  have hc : (QuotientGroup.mk ⟨x, hx⟩ : T ⧸ K) * QuotientGroup.mk ⟨y, hy⟩ =
      QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨x, hx⟩ := by
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self g m n).eq
  have h1 : ((⟨x, hx⟩ : T) * ⟨y, hy⟩ * (⟨x, hx⟩ : T)⁻¹ * (⟨y, hy⟩ : T)⁻¹) ∈ K := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc]
    group
  exact Subgroup.mem_subgroupOf.1 h1

omit [Finite G] in
theorem mem_centralizer_singleton {z h : G} :
    h ∈ Subgroup.centralizer ({z} : Set G) ↔ z * h = h * z := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro H; exact H z rfl
  · intro H g hg; rw [Set.mem_singleton_iff.1 hg]; exact H

omit [Finite G] in
theorem mem_centralizer_conj {c z h : G} :
    h ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set G) ↔
      c⁻¹ * h * c ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton, mem_centralizer_singleton]
  constructor
  · intro H
    calc z * (c⁻¹ * h * c) = c⁻¹ * ((c * z * c⁻¹) * h) * c := by group
      _ = c⁻¹ * (h * (c * z * c⁻¹)) * c := by rw [H]
      _ = (c⁻¹ * h * c) * z := by group
  · intro H
    calc (c * z * c⁻¹) * h = c * (z * (c⁻¹ * h * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * h * c) * z) * c⁻¹ := by rw [H]
      _ = h * (c * z * c⁻¹) := by group

omit [Finite G] in
theorem comm_conj {z h t v : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G))
    (hc : (h * t * h⁻¹) * v * (h * t * h⁻¹)⁻¹ * v⁻¹ = 1 ∨
      (h * t * h⁻¹) * v * (h * t * h⁻¹)⁻¹ * v⁻¹ = z) :
    t * (h⁻¹ * v * h) * t⁻¹ * (h⁻¹ * v * h)⁻¹ = 1 ∨
      t * (h⁻¹ * v * h) * t⁻¹ * (h⁻¹ * v * h)⁻¹ = z := by
  have hzh := mem_centralizer_singleton.1 hh
  have hz : h⁻¹ * z * h = z := by
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hzh]
      _ = z := by group
  have e : t * (h⁻¹ * v * h) * t⁻¹ * (h⁻¹ * v * h)⁻¹ =
      h⁻¹ * ((h * t * h⁻¹) * v * (h * t * h⁻¹)⁻¹ * v⁻¹) * h := by group
  rw [e]
  rcases hc with h1 | h1
  · left; rw [h1]; group
  · right; rw [h1, hz]

omit [Finite G] in
@[expose] def commSub (z v : G) (hz2 : z * z = 1) : Subgroup G where
  carrier := {p | p ∈ Subgroup.centralizer ({z} : Set G) ∧
    (p * v * p⁻¹ * v⁻¹ = 1 ∨ p * v * p⁻¹ * v⁻¹ = z)}
  one_mem' := ⟨Subgroup.one_mem _, Or.inl (by group)⟩
  mul_mem' := by
    rintro p₁ p₂ ⟨h₁, hc₁⟩ ⟨h₂, hc₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, ?_⟩
    have hz1 := mem_centralizer_singleton.1 h₁
    have hzc : p₁ * z * p₁⁻¹ = z := by
      calc p₁ * z * p₁⁻¹ = (p₁ * z) * p₁⁻¹ := rfl
        _ = (z * p₁) * p₁⁻¹ := by rw [← hz1]
        _ = z := by group
    have e : p₁ * p₂ * v * (p₁ * p₂)⁻¹ * v⁻¹ =
        (p₁ * (p₂ * v * p₂⁻¹ * v⁻¹) * p₁⁻¹) * (p₁ * v * p₁⁻¹ * v⁻¹) := by group
    rw [e]
    rcases hc₂ with h2 | h2 <;> rcases hc₁ with h1 | h1
    · left; rw [h1, h2]; group
    · right; rw [h1, h2]; group
    · right; rw [h2, hzc, h1]; group
    · left; rw [h2, hzc, h1, hz2]
  inv_mem' := by
    rintro p ⟨hp, hc⟩
    refine ⟨Subgroup.inv_mem _ hp, ?_⟩
    have hz1 := mem_centralizer_singleton.1 hp
    have hzc : p⁻¹ * z * p = z := by
      calc p⁻¹ * z * p = p⁻¹ * (z * p) := by group
        _ = p⁻¹ * (p * z) := by rw [← hz1]
        _ = z := by group
    have e : p⁻¹ * v * p⁻¹⁻¹ * v⁻¹ = p⁻¹ * (p * v * p⁻¹ * v⁻¹)⁻¹ * p := by group
    rw [e]
    rcases hc with h1 | h1
    · left; rw [h1]; group
    · right
      have hzi : z⁻¹ = z := by
        calc z⁻¹ = z⁻¹ * (z * z) := by rw [hz2]; group
          _ = z := by group
      rw [h1, hzi, hzc]

omit [Finite G] in
theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem card_le_two_mul_inf_centralizer {X : Subgroup G} {c w : G}
    (hX : ∀ x ∈ X, x ∈ Subgroup.centralizer ({c} : Set G) ∨ x * c * x⁻¹ = w * c) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set R : Subgroup G := X ⊓ C with hR
  by_cases hall : ∀ q ∈ X, q ∈ R
  · have hle : X ≤ R := hall
    have := Subgroup.card_le_of_le hle
    omega
  · push Not at hall
    obtain ⟨q₂, hq₂, hq₂R⟩ := hall
    have hq₂C : q₂ ∉ C := fun hh => hq₂R ⟨hq₂, hh⟩
    have h2 : q₂ * c * q₂⁻¹ = w * c := (hX q₂ hq₂).resolve_left hq₂C
    have hsub : (X : Set G) ⊆ (R : Set G) ∪ ((fun r => q₂ * r) '' (R : Set G)) := by
      intro q hq
      by_cases hqR : q ∈ R
      · exact Or.inl hqR
      · right
        have hqC : q ∉ C := fun hh => hqR ⟨hq, hh⟩
        have h1 : q * c * q⁻¹ = w * c := (hX q hq).resolve_left hqC
        refine ⟨q₂⁻¹ * q, ⟨X.mul_mem (X.inv_mem hq₂) hq, ?_⟩, by group⟩
        refine mem_centralizer_singleton.2 ?_
        calc c * (q₂⁻¹ * q) = q₂⁻¹ * (q₂ * c * q₂⁻¹) * q := by group
          _ = q₂⁻¹ * (q * c * q⁻¹) * q := by rw [h1, h2]
          _ = (q₂⁻¹ * q) * c := by group
    have h1 : Nat.card X = (X : Set G).ncard := Nat.card_coe_set_eq _
    have h2' : Nat.card R = (R : Set G).ncard := Nat.card_coe_set_eq _
    have h3 : ((fun r => q₂ * r) '' (R : Set G)).ncard = (R : Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_right_injective q₂)
    calc Nat.card X = (X : Set G).ncard := h1
      _ ≤ ((R : Set G) ∪ ((fun r => q₂ * r) '' (R : Set G))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (R : Set G).ncard + ((fun r => q₂ * r) '' (R : Set G)).ncard :=
        Set.ncard_union_le _ _
      _ = 2 * Nat.card R := by rw [h3, h2']; ring

theorem card_le_two_of_forall {z : G} {K : Subgroup G} (h : ∀ w ∈ K, w = 1 ∨ w = z) :
    Nat.card K ≤ 2 := by
  have hsub : (K : Set G) ⊆ {1, z} := fun w hw => by
    rcases h w hw with rfl | rfl <;> simp
  calc Nat.card K = (K : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem card_abelian_le_eight {z : G} {Q : Subgroup G} (hQcard : Nat.card Q = 32)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQZ : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z) {A : Subgroup G}
    (hAQ : A ≤ Q) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 8 := by
  classical
  by_contra hgt
  push Not at hgt
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAQ
  rw [hQcard] at hm
  have hm3 : m ≤ 3 := by
    by_contra h
    push Not at h
    have : Nat.card A * 4 ≤ Nat.card A * m := Nat.mul_le_mul_left _ h
    omega
  interval_cases m
  · omega
  · exfalso
    have hAQ' : A = Q := Subgroup.eq_of_le_of_card_ge hAQ (by omega)
    subst hAQ'
    have := card_le_two_of_forall (K := A) fun w hw => hQZ w hw fun q hq => hA q hq w hw
    omega
  · have hidx : Nat.card Q = 2 * Nat.card A := by omega
    have hex : ∃ q ∈ Q, q ∉ A := by
      by_contra hno
      push Not at hno
      have hle : Q ≤ A := hno
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨q, hqQ, hqA⟩ := hex
    have hdich := (normal_dichotomy hAQ hidx hqQ hqA).2
    have hcard := card_le_two_mul_inf_centralizer (X := A) (c := q) (w := z) fun x hx => by
      rcases hQcomm x (hAQ hx) q hqQ with h | h
      · left
        refine mem_centralizer_singleton.2 ?_
        have h1 : x * q * x⁻¹ = q := mul_inv_eq_one.1 h
        calc q * x = (x * q * x⁻¹) * x := by rw [h1]
          _ = x * q := by group
      · right
        calc x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
          _ = z * q := by rw [h]
    have hKz : ∀ w ∈ (A ⊓ Subgroup.centralizer ({q} : Set G) : Subgroup G), w = 1 ∨ w = z := by
      intro w hw
      have hwq : q * w = w * q := mem_centralizer_singleton.1 hw.2
      refine hQZ w (hAQ hw.1) fun x hx => ?_
      rcases hdich x hx with hxA | hxA
      · exact hA x hxA w hw.1
      · have hx : x = q * (q⁻¹ * x) := by group
        rw [hx]
        calc q * (q⁻¹ * x) * w = q * ((q⁻¹ * x) * w) := by group
          _ = q * (w * (q⁻¹ * x)) := by rw [hA _ hxA w hw.1]
          _ = (q * w) * (q⁻¹ * x) := by group
          _ = (w * q) * (q⁻¹ * x) := by rw [hwq]
          _ = w * (q * (q⁻¹ * x)) := by group
    have := card_le_two_of_forall hKz
    omega
  · omega

end CFSG.Quasithin.H13.F431.G2Two
