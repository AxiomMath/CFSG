module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

namespace EvenFin

variable {G : Type} [Group G]

theorem comm_mul_right_of_commute {w u c : G} (h : u * c = c * u) :
    (w * u) * c * (w * u)⁻¹ * c⁻¹ = w * c * w⁻¹ * c⁻¹ := by
  have e : u * c * u⁻¹ = c := by rw [h]; group
  calc (w * u) * c * (w * u)⁻¹ * c⁻¹ = w * (u * c * u⁻¹) * w⁻¹ * c⁻¹ := by group
    _ = w * c * w⁻¹ * c⁻¹ := by rw [e]

theorem comm_mul_left_of_commute {w y₁ y₂ : G}
    (h : y₁ * (w * y₂ * w⁻¹ * y₂⁻¹) = (w * y₂ * w⁻¹ * y₂⁻¹) * y₁) :
    w * (y₁ * y₂) * w⁻¹ * (y₁ * y₂)⁻¹ = (w * y₁ * w⁻¹ * y₁⁻¹) * (w * y₂ * w⁻¹ * y₂⁻¹) := by
  calc w * (y₁ * y₂) * w⁻¹ * (y₁ * y₂)⁻¹
      = w * y₁ * w⁻¹ * y₁⁻¹ * (y₁ * (w * y₂ * w⁻¹ * y₂⁻¹)) * y₁⁻¹ := by group
    _ = w * y₁ * w⁻¹ * y₁⁻¹ * ((w * y₂ * w⁻¹ * y₂⁻¹) * y₁) * y₁⁻¹ := by rw [h]
    _ = (w * y₁ * w⁻¹ * y₁⁻¹) * (w * y₂ * w⁻¹ * y₂⁻¹) := by group

theorem conj_comm (g w y : G) :
    g * (w * y * w⁻¹ * y⁻¹) * g⁻¹ =
      (g * w * g⁻¹) * (g * y * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by
  group

theorem commute_of_comm_eq {w y₁ y₂ : G} (h : w * y₁ * w⁻¹ * y₁⁻¹ = w * y₂ * w⁻¹ * y₂⁻¹) :
    w * (y₁⁻¹ * y₂) = (y₁⁻¹ * y₂) * w := by
  have h2 : y₁ * w * y₁⁻¹ = y₂ * w * y₂⁻¹ := by
    have e1 : (w * y₁ * w⁻¹ * y₁⁻¹)⁻¹ * w = y₁ * w * y₁⁻¹ := by group
    have e2 : (w * y₂ * w⁻¹ * y₂⁻¹)⁻¹ * w = y₂ * w * y₂⁻¹ := by group
    rw [← e1, ← e2, h]
  calc w * (y₁⁻¹ * y₂) = y₁⁻¹ * (y₁ * w * y₁⁻¹) * y₂ := by group
    _ = y₁⁻¹ * (y₂ * w * y₂⁻¹) * y₂ := by rw [h2]
    _ = (y₁⁻¹ * y₂) * w := by group

theorem comm_eq_of_commute {u a c : G} (hp : u * (a * c⁻¹) = (a * c⁻¹) * u)
    (hq : (a * c⁻¹) * (u * c * u⁻¹ * c⁻¹) = (u * c * u⁻¹ * c⁻¹) * (a * c⁻¹)) :
    u * a * u⁻¹ * a⁻¹ = u * c * u⁻¹ * c⁻¹ := by
  calc u * a * u⁻¹ * a⁻¹ = (u * (a * c⁻¹)) * c * u⁻¹ * c⁻¹ * (a * c⁻¹)⁻¹ := by group
    _ = ((a * c⁻¹) * u) * c * u⁻¹ * c⁻¹ * (a * c⁻¹)⁻¹ := by rw [hp]
    _ = ((a * c⁻¹) * (u * c * u⁻¹ * c⁻¹)) * (a * c⁻¹)⁻¹ := by group
    _ = ((u * c * u⁻¹ * c⁻¹) * (a * c⁻¹)) * (a * c⁻¹)⁻¹ := by rw [hq]
    _ = u * c * u⁻¹ * c⁻¹ := by group

theorem comm_conj_right (u x y : G) :
    u * (x * y * x⁻¹) * u⁻¹ * (x * y * x⁻¹)⁻¹ =
      x * ((x⁻¹ * u * x) * y * (x⁻¹ * u * x)⁻¹ * y⁻¹) * x⁻¹ := by
  group

theorem conj_mem_centralizer {W : Subgroup G} {g n : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (hn : n ∈ Subgroup.centralizer (W : Set G)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro w hw
  have hw' : g⁻¹ * w * g ∈ W := by
    refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * w * g)).mpr ?_
    have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    rw [e]
    exact hw
  have := hn _ hw'
  calc w * (g * n * g⁻¹) = g * ((g⁻¹ * w * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
    _ = g * n * g⁻¹ * w := by group

theorem conj_mem_inf_centralizer_iff {W C : Subgroup G} {g : G}
    (hW : g ∈ Subgroup.normalizer (W : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G))
    (u : G) :
    g * u * g⁻¹ ∈ W ⊓ Subgroup.centralizer (C : Set G) ↔
      u ∈ W ⊓ Subgroup.centralizer (C : Set G) := by
  constructor
  · rintro ⟨hW', hC'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hW u).mpr hW', ?_⟩
    have hg' : g⁻¹ ∈ Subgroup.normalizer (C : Set G) := inv_mem hC
    have := conj_mem_centralizer hg' hC'
    have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rwa [e] at this
  · rintro ⟨hW', hC'⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hW u).mp hW', conj_mem_centralizer hC hC'⟩

theorem mem_normalizer_of_conj_le [Finite G] {U : Subgroup G} {x : G}
    (h : ∀ u ∈ U, x * u * x⁻¹ ∈ U) : x ∈ Subgroup.normalizer (U : Set G) := by
  have hle : Subgroup.map (MulAut.conj x : G →* G) U ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

theorem exists_fixed_of_le_normalizer [Finite G] {P I : Subgroup G} (hP : IsPGroup 2 P)
    (hI : IsPGroup 2 I) (hn : P ≤ Subgroup.normalizer (I : Set G)) (hne : I ≠ ⊥) :
    ∃ i ∈ I, i ≠ 1 ∧ ∀ p ∈ P, p * i * p⁻¹ = i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥P ↥I :=
    { smul := fun p i => ⟨(p : G) * i * (p : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hn p.2) i).mp i.2⟩
      one_smul := fun i => Subtype.ext (show (1 : G) * i * 1⁻¹ = i by group)
      mul_smul := fun p q i => Subtype.ext (show ((p : G) * q) * i * ((p : G) * q)⁻¹ =
        (p : G) * ((q : G) * i * (q : G)⁻¹) * (p : G)⁻¹ by group) }
  have hdvd : 2 ∣ Nat.card I := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hI
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq I (by simpa using hn))
    exact hn ▸ dvd_pow_self 2 hn0
  have h1 : (1 : ↥I) ∈ MulAction.fixedPoints ↥P ↥I := fun p =>
    Subtype.ext (show (p : G) * 1 * (p : G)⁻¹ = 1 by group)
  obtain ⟨b, hb, hne'⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥I hdvd h1
  refine ⟨b, b.2, fun h => hne' (Subtype.ext h.symm), fun p hp => ?_⟩
  exact congrArg Subtype.val (hb ⟨p, hp⟩)

end EvenFin

end CFSG.Quasithin.F53.Stellmacher.S43.Even
