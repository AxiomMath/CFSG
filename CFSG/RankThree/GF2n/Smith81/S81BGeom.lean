module

public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81.EGeom

open CFSG CFSG.RankThree.GF2n.Stroth80

section Model

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def conjSub (g : V ≃ₗ[K] V) (U : Subgroup (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V) :=
  U.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g : V ≃ₗ[K] V} {U : Subgroup (V ≃ₗ[K] V)} {u : V ≃ₗ[K] V} :
    u ∈ conjSub g U ↔ ∃ u₀ ∈ U, g * u₀ * g⁻¹ = u := by
  simp [conjSub, Subgroup.mem_map]

@[expose] def Wsp (L : Submodule K V) (R : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ u ∈ R, u v - v ∈ L}
  add_mem' := fun {a b} ha hb u hu => by
    have h := L.add_mem (ha u hu) (hb u hu)
    rwa [map_add, show u a + u b - (a + b) = (u a - a) + (u b - b) by abel]
  zero_mem' := fun u _ => by simp
  smul_mem' := fun c v hv u hu => by
    have h := L.smul_mem c (hv u hu)
    rwa [map_smul, ← smul_sub]

theorem mem_Wsp {L : Submodule K V} {R : Subgroup (V ≃ₗ[K] V)} {v : V} :
    v ∈ Wsp L R ↔ ∀ u ∈ R, u v - v ∈ L := Iff.rfl

theorem Wsp_map (g : V ≃ₗ[K] V) (L : Submodule K V) (R : Subgroup (V ≃ₗ[K] V)) :
    Wsp (L.map (g : V →ₗ[K] V)) (conjSub g R) = (Wsp L R).map (g : V →ₗ[K] V) := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨g.symm v, fun u hu => ?_, by simp⟩
    have h := hv (g * u * g⁻¹) (mem_conjSub.mpr ⟨u, hu, rfl⟩)
    obtain ⟨l, hl, hl'⟩ := Submodule.mem_map.mp h
    have h2 : (g : V →ₗ[K] V) (u (g.symm v) - g.symm v) = (g * u * g⁻¹) v - v := by
      simp [map_sub]
    have h3 : u (g.symm v) - g.symm v = l := g.injective (h2.trans hl'.symm)
    rw [h3]
    exact hl
  · rintro ⟨w, hw, rfl⟩ u hu
    obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.mp hu
    refine Submodule.mem_map.mpr ⟨u₀ w - w, hw u₀ hu₀, ?_⟩
    simp [map_sub]

theorem card_Wsp_conj (g : V ≃ₗ[K] V) (L : Submodule K V) (R : Subgroup (V ≃ₗ[K] V)) :
    Nat.card (Wsp (L.map (g : V →ₗ[K] V)) (conjSub g R)) = Nat.card (Wsp L R) := by
  rw [Wsp_map]
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective (g : V →ₗ[K] V) g.injective (Wsp L R)).toEquiv).symm

structure MinuscGeom (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V))
    (n : ℕ) : Prop where
  p₀_ne : p₀ ≠ 0
  U₀_le : U₀ ≤ Γ
  U₀_fix : ∀ u ∈ U₀, u p₀ = p₀
  W_le : Nat.card (Wsp (Submodule.span K {p₀}) U₀) ≤ Nat.card K ^ n
  line : ∃ g₁ ∈ Γ, g₁ p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ ∧
    g₁ p₀ ∉ Submodule.span K {p₀} ∧
    ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → ∃ g ∈ Γ, g p₀ = a • p₀ + b • g₁ p₀

end Model

section Data

open CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G] {K : Type} [Field K] {γ : G → K} {V : Type} [AddCommGroup V]
  [Module K V]

structure EUniData (M Q Z B : Subgroup G) (M₀ : Tim79.QuadModel Q Z K γ) (ψ : M₀.E ≃ₗ[K] V)
    (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)) (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V)
    (U₀ : Subgroup (V ≃ₗ[K] V)) : Prop where
  range : φ.range = Γ
  ker : ∀ s : Lgen M (LB M Q B), φ s = 1 ↔ (s : G) ∈ Q
  le_normalizer : Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G)
  equivariant : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
    ψ (M₀.π ((s : G) * x * (s : G)⁻¹)) = φ s (ψ (M₀.π x))
  point : ∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q → A ≠ Z → ∃ g ∈ Γ,
    (fun a : G => ψ (M₀.π a)) '' (A : Set G) = (Submodule.span K {g p₀} : Set V) ∧
    ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A ∧ φ t = u

end Data

end CFSG.RankThree.GF2n.Smith81.EGeom
