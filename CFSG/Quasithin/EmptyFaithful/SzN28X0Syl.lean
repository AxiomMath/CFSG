module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Grp
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.SzN28

variable {G : Type*} [Group G]

theorem central_mem_sylow_two [Finite G] {C S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ (S.subgroupOf C).index) {t : G} (htC : t ∈ C) (ht2 : t * t = 1)
    (htc : ∀ g ∈ C, g * t = t * g) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t₀ : ↥C := ⟨t, htC⟩
  let N : Subgroup ↥C := Subgroup.zpowers t₀
  have hcomm : ∀ g : ↥C, Commute g t₀ := fun g => Subtype.ext (htc g g.2)
  have : N.Normal := ⟨fun n hn g => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h1 : g * t₀ ^ m = t₀ ^ m * g := (Commute.zpow_right (hcomm g) m).eq
    rw [mul_inv_eq_iff_eq_mul.2 h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t₀) m⟩
  have hN2 : IsPGroup 2 N := by
    have h2 : t₀ * t₀ = 1 := Subtype.ext ht2
    have hord : orderOf t₀ ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact h2)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  have hS'2 : IsPGroup 2 (S.subgroupOf C) := hS2.comap_subtype
  let Q : Sylow 2 ↥C := hS'2.toSylow hSidx
  have h1 : N ≤ (Q : Subgroup ↥C) := hN2.le_sylow_of_normal Q
  exact h1 (Subgroup.mem_zpowers t₀)

theorem exists_central_of_normal [Finite G] {S X : Subgroup G} (hS2 : IsPGroup 2 S) (hXS : X ≤ S)
    (hSN : S ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) :
    ∃ z ∈ X, z ≠ 1 ∧ ∀ s ∈ S, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS2.isNilpotent
  let H : Subgroup ↥S := X.subgroupOf S
  have : H.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXS).2 hSN
  have hH : H ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hXS hx⟩ : ↥S) ∈ H := hx
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  refine ⟨(z : G), hz.1, fun h => hz1 ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact h
  · have := Subgroup.mem_center_iff.1 hz.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

theorem t_mem_X [Finite G] {Γ S X : Subgroup G} (e : ↥Γ ≃* Equiv.Perm (Fin 8)) (hSΓ : S ≤ Γ)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ (S.subgroupOf Γ).index) (hXS : X ≤ S)
    (hSN : S ≤ Subgroup.normalizer (X : Set G)) (hX : X ≠ ⊥) {t : G} (htS : t ∈ S) (ht1 : t ≠ 1)
    (htc : ∀ s ∈ S, s * t = t * s) : t ∈ X := by
  obtain ⟨z, hzX, hz1, hzc⟩ := exists_central_of_normal hS2 hXS hSN hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S₀ : Subgroup ↥Γ := S.subgroupOf Γ
  let S' : Subgroup (Equiv.Perm (Fin 8)) := S₀.map (e : ↥Γ →* Equiv.Perm (Fin 8))
  have hS₀2 : IsPGroup 2 S₀ := hS2.comap_subtype
  have hS'2 : IsPGroup 2 S' := hS₀2.map _
  have hS'idx : ¬ 2 ∣ S'.index := by
    rw [Subgroup.index_map_equiv]
    exact hSidx
  let zΓ : ↥Γ := ⟨z, hSΓ (hXS hzX)⟩
  let tΓ : ↥Γ := ⟨t, hSΓ htS⟩
  have hmem : ∀ g : ↥Γ, (g : G) ∈ S → e g ∈ S' := fun g hg => ⟨g, hg, rfl⟩
  have hcent : ∀ (u : ↥Γ), (∀ s ∈ S, s * (u : G) = (u : G) * s) → ∀ σ ∈ S', e u * σ = σ * e u := by
    intro u hcu σ hσ
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hσ
    change e u * e g = e g * e u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcu g hg).symm
  rcases center_sylow_two_perm8 hS'2 hS'idx (hmem zΓ (hXS hzX)) (hmem tΓ htS)
    (hcent zΓ hzc) (hcent tΓ htc) with h | h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hz1
  · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) ht1
  · have h1 : zΓ = tΓ := e.injective h
    have h2 : z = t := congrArg Subtype.val h1
    rw [← h2]
    exact hzX

end CFSG.Quasithin.SzN28
