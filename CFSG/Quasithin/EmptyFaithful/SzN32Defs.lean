module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.SzN32

variable {G : Type*} [Group G]

@[expose] def IsE27 (E : Subgroup G) : Prop :=
  Nat.card E = 27 ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ∀ x ∈ E, ∀ y ∈ E, x * y = y * x

@[expose] def cm (g h : G) : G := g⁻¹ * h⁻¹ * g * h

structure TData {S : Type*} [Group S] (a σ : S) : Prop where
  gen : Subgroup.closure ({a, σ} : Set S) = ⊤
  a_cube : a ^ 3 = 1
  u_comm_a : cm a σ * a = a * cm a σ
  z_comm_a : cm (cm a σ) σ * a = a * cm (cm a σ) σ
  z_comm_σ : cm (cm a σ) σ * σ = σ * cm (cm a σ) σ
  z_ne_one : cm (cm a σ) σ ≠ 1
  u_not_mem : cm a σ ∉ Subgroup.zpowers (cm (cm a σ) σ)
  u_cube : cm a σ ^ 3 = 1
  z_cube : cm (cm a σ) σ ^ 3 = 1
  e27 : ∃ D : Subgroup S, IsE27 D

theorem map_cm {H : Type*} [Group H] (f : G →* H) (g h : G) : f (cm g h) = cm (f g) (f h) := by
  simp [cm]

theorem IsE27.map_mulEquiv {H : Type*} [Group H] (f : G ≃* H) {E : Subgroup G} (hE : IsE27 E) :
    IsE27 (E.map f.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective f.injective]
    exact h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h3 x hx y hy]

theorem TData.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (f : S ≃* S') {a σ : S}
    (h : TData a σ) : TData (f a) (f σ) := by
  have hu : ∀ x y : S, f (cm x y) = cm (f x) (f y) := fun x y => map_cm f.toMonoidHom x y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map f.toMonoidHom) h.gen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ f.surjective] at this
    simpa [Set.image_pair] using this
  · rw [← map_pow, h.a_cube, map_one]
  · rw [← hu, ← map_mul, ← map_mul, h.u_comm_a]
  · rw [← hu, ← hu, ← map_mul, ← map_mul, h.z_comm_a]
  · rw [← hu, ← hu, ← map_mul, ← map_mul, h.z_comm_σ]
  · rw [← hu, ← hu]
    exact fun h1 => h.z_ne_one (f.injective (by rw [h1, map_one]))
  · rw [← hu, ← hu]
    intro hmem
    refine h.u_not_mem ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨k, f.injective (by rw [map_zpow]; exact hk)⟩
  · rw [← hu, ← map_pow, h.u_cube, map_one]
  · rw [← hu, ← hu, ← map_pow, h.z_cube, map_one]
  · obtain ⟨D, hD⟩ := h.e27
    exact ⟨D.map f.toMonoidHom, hD.map_mulEquiv f⟩

end CFSG.Quasithin.SzN32
