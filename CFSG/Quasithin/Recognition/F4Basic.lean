module

public import CFSG.Quasithin.Background.F3Amalgam
public import CFSG.Quasithin.Background.F3Geodesic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.F7

universe u w

@[expose] def IsComplementIn {H : Type*} [Group H] (K Q M : Subgroup H) : Prop :=
  Q ≤ M ∧ K ≤ M ∧ Q ⊓ K = ⊥ ∧ ∀ g ∈ M, ∃ q ∈ Q, ∃ k ∈ K, q * k = g

namespace IsComplementIn

variable {H : Type*} [Group H] {K Q M : Subgroup H}

theorem inf_left (h : IsComplementIn K Q M) {M' : Subgroup H} (hQ : Q ≤ M') (hM' : M' ≤ M) :
    IsComplementIn (K ⊓ M') Q M' := by
  refine ⟨hQ, inf_le_right, ?_, fun g hg => ?_⟩
  · refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ Q ⊓ K := ⟨hx.1, hx.2.1⟩
    rw [h.2.2.1] at this
    exact this
  · obtain ⟨q, hq, k, hk, rfl⟩ := h.2.2.2 g (hM' hg)
    refine ⟨q, hq, k, ⟨hk, ?_⟩, rfl⟩
    have := M'.mul_mem (M'.inv_mem (hQ hq)) hg
    simpa using this

theorem comap_iff {A : Type*} [Group A] (f : A →* H) (hf : Function.Injective f)
    (hK : K ≤ f.range) (hQ : Q ≤ f.range) (hM : M ≤ f.range) :
    IsComplementIn K Q M ↔ IsComplementIn (K.comap f) (Q.comap f) (M.comap f) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨Subgroup.comap_mono h1, Subgroup.comap_mono h2, ?_, fun a ha => ?_⟩
    · refine eq_bot_iff.mpr fun a ha => ?_
      have : f a ∈ Q ⊓ K := ⟨ha.1, ha.2⟩
      rw [h3] at this
      have h0 : f a = 1 := this
      rw [Subgroup.mem_bot]
      exact hf (by rw [h0, map_one])
    · obtain ⟨q, hq, k, hk, hqk⟩ := h4 (f a) ha
      obtain ⟨q', rfl⟩ := hQ hq
      obtain ⟨k', rfl⟩ := hK hk
      exact ⟨q', hq, k', hk, hf (by rw [map_mul]; exact hqk)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, fun g hg => ?_⟩
    · obtain ⟨x', rfl⟩ := hQ hx
      exact h1 hx
    · obtain ⟨x', rfl⟩ := hK hx
      exact h2 hx
    · refine eq_bot_iff.mpr fun x hx => ?_
      obtain ⟨x', rfl⟩ := hQ hx.1
      have : x' ∈ Q.comap f ⊓ K.comap f := ⟨hx.1, hx.2⟩
      rw [h3, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    · obtain ⟨g', rfl⟩ := hM hg
      obtain ⟨q', hq', k', hk', rfl⟩ := h4 g' hg
      exact ⟨f q', hq', f k', hk', (map_mul f q' k').symm⟩

theorem conjSub_iff (g : H) :
    IsComplementIn (conjSub g K) (conjSub g Q) (conjSub g M) ↔ IsComplementIn K Q M := by
  have key : ∀ (g : H) {K Q M : Subgroup H}, IsComplementIn K Q M →
      IsComplementIn (conjSub g K) (conjSub g Q) (conjSub g M) := by
    rintro g K Q M ⟨h1, h2, h3, h4⟩
    refine ⟨conjSub_mono g h1, conjSub_mono g h2, ?_, fun x hx => ?_⟩
    · rw [← conjSub_inf, h3, conjSub_bot]
    · rw [mem_conjSub] at hx
      obtain ⟨q, hq, k, hk, hqk⟩ := h4 _ hx
      refine ⟨g * q * g⁻¹, mul_mem_conjSub hq, g * k * g⁻¹, mul_mem_conjSub hk, ?_⟩
      calc g * q * g⁻¹ * (g * k * g⁻¹) = g * (q * k) * g⁻¹ := by group
        _ = x := by rw [hqk]; group
  refine ⟨fun h => ?_, key g⟩
  have := key g⁻¹ h
  simpa [conjSub_conjSub_inv] using this

end IsComplementIn

structure IsGenPolygon {V : Type*} (Γ : SimpleGraph V) (m : ℕ) : Prop where
  connected : Γ.Connected
  bipartite : ∃ c : V → Bool, ∀ a b, Γ.Adj a b → c a ≠ c b
  diam_le : ∀ u v, Γ.dist u v ≤ m
  diam_eq : ∃ u v, Γ.dist u v = m
  uniqueGeod : UniqueGeod Γ m
  polygon : ∃ S : Set V, IsPolygon Γ S (2 * m)
  valence : ∀ v, 2 ≤ (Γ.neighborSet v).encard

namespace RankTwoAmalgam

variable (α : RankTwoAmalgam.{u})

@[expose] noncomputable def qOne : ℕ := α.α1.range.index - 1

@[expose] noncomputable def qTwo : ℕ := α.α2.range.index - 1

end RankTwoAmalgam

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

abbrev G0 (c : α.Completion Y) : Type w := ↥(c.φ1.range ⊔ c.φ2.range)

abbrev xv (c : α.Completion Y) : c.Γ :=
  CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range

abbrev lv (c : α.Completion Y) : c.Γ :=
  CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range

abbrev stv (c : α.Completion Y) (u : c.Γ) : Subgroup c.G0 := MulAction.stabilizer c.G0 u

@[expose] def PathTrans (c : α.Completion Y) (u : c.Γ) (n : ℕ) : Prop :=
  ∀ q q' : GPath c.graph n, q ∈ GPath.nbPaths c.graph u n → q' ∈ GPath.nbPaths c.graph u n →
    ∃ g : c.G0, g • u = u ∧ g • q = q'

@[expose] def IsLarge (c : α.Completion Y) (m : ℕ) : Prop :=
  ∀ p q : GPath c.graph m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p m = q m → p = q

@[expose] def IsSmall (c : α.Completion Y) (m : ℕ) : Prop := ¬ c.IsLarge m

@[expose] def geods (c : α.Completion Y) (m : ℕ) (a b : c.Γ) : Set (GPath c.graph m) :=
  {t | t 0 = a ∧ t m = b ∧ t.IsGeodesic}

@[expose] def IsApartment (c : α.Completion Y) (m : ℕ) (S : Set c.Γ) : Prop :=
  IsPolygon c.graph S (2 * m)

end RankTwoAmalgam.Completion

end CFSG.Quasithin
