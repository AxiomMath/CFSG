module

public import CFSG.Quasithin.Background.RonanE611Aux
public import CFSG.Quasithin.Background.RonanE611Gen

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem mem_normalizer_normalizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have hS : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.1 hg
  constructor
  · intro hx s
    have h1 := hx (g⁻¹ * s * g)
    have h2 := hS (g⁻¹ * s * g)
    have h3 := hS (x * (g⁻¹ * s * g) * x⁻¹)
    rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h2
    have e : g * x * g⁻¹ * s * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * s * g) * x⁻¹) * g⁻¹ := by group
    rw [e, ← h3, ← h1, h2]
  · intro hx s
    have h1 := hx (g * s * g⁻¹)
    have h2 := hS s
    have h3 := hS (x * s * x⁻¹)
    have e : g * x * g⁻¹ * (g * s * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * s * x⁻¹) * g⁻¹ := by group
    rw [e] at h1
    rw [h2, h1, ← h3]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem mem_normalizer_centerOf {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer ((centerOf S : Subgroup G) : Set G) := by
  have hS : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hcen : ∀ z, z ∈ centerOf S ↔ z ∈ S ∧ ∀ s ∈ S, s * z = z * s := fun z => by
    rw [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have key : ∀ z, (z ∈ S ∧ ∀ s ∈ S, s * z = z * s) →
      (g * z * g⁻¹ ∈ S ∧ ∀ s ∈ S, s * (g * z * g⁻¹) = (g * z * g⁻¹) * s) := by
    rintro z ⟨hz, hzc⟩
    refine ⟨(hS z).1 hz, fun s hs => ?_⟩
    have h1 := hzc (g⁻¹ * s * g) ((by
      have := hS (g⁻¹ * s * g)
      rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at this
      exact this.2 hs))
    have e1 : s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
    have e2 : (g * z * g⁻¹) * s = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by group
    rw [e1, e2, h1]
  rw [hcen, hcen]
  constructor
  · exact key z
  · intro h
    have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hg
    have hS' : ∀ s, s ∈ S ↔ g⁻¹ * s * g⁻¹⁻¹ ∈ S := Subgroup.mem_normalizer_iff.1 hg'
    obtain ⟨h1, h2⟩ := h
    refine ⟨(hS z).2 h1, fun s hs => ?_⟩
    have h3 := h2 (g * s * g⁻¹) ((hS s).1 hs)
    have e1 : g * s * g⁻¹ * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by group
    have e2 : g * z * g⁻¹ * (g * s * g⁻¹) = g * (z * s) * g⁻¹ := by group
    rw [e1, e2] at h3
    exact mul_left_cancel (mul_right_cancel h3)

theorem mem_normalizer_inf_normalizer {L S : Subgroup G} {g : G}
    (hL : g ∈ Subgroup.normalizer (L : Set G)) (hS : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf hL (mem_normalizer_normalizer hS)

theorem mem_normalizer_of_centralizes {U : Subgroup G} {g : G} (hg : ∀ u ∈ U, g * u = u * g)
    (hg' : ∀ u ∈ U, g⁻¹ * u = u * g⁻¹) : g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [hg u hu]
    simpa using hu
  · intro hu
    have h1 := hg' _ hu
    rw [show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group] at h1
    have h3 : u = g * u * g⁻¹ := mul_right_cancel h1
    rw [h3]
    exact hu

end Conj

section Main

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup {U W : Subgroup G} {g : G}
    (hU : g ∈ Subgroup.normalizer (U : Set G)) (hW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((U ⊔ W : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hU, map_conj_eq_of_mem_normalizer hW]

theorem normalizer_le_of_lin {H L S V U W : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHU : ∀ g ∈ H, ∀ u ∈ U, g * u = u * g)
    (hsup : U ⊔ W = V)
    (hD : ⁅centerOf S, L ⊓ Subgroup.normalizer (S : Set G)⁆ = W) {g : G} (hgH : g ∈ H)
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) : g ∈ Subgroup.normalizer (V : Set G) := by
  have hgL := hHL hgH
  have hgW : g ∈ Subgroup.normalizer (W : Set G) := by
    rw [← hD]
    exact mem_normalizer_commutator (mem_normalizer_centerOf hgS)
      (mem_normalizer_inf_normalizer hgL hgS)
  have hgU : g ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_of_centralizes (hHU g hgH) (hHU g⁻¹ (H.inv_mem hgH))
  rw [← hsup]
  exact mem_normalizer_sup hgU hgW

theorem normalizer_le_of_two_roots {H L S Q V U W W₁ W₂ : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHU : ∀ g ∈ H, ∀ u ∈ U, g * u = u * g)
    (hsup : U ⊔ W = V) (hQ : IsSylowTwoOf Q (H ⊓ Subgroup.normalizer (S : Set G)))
    (hQW : Q ≤ Subgroup.normalizer (W : Set G))
    (hroots : ∀ W' : Subgroup G, W' ≤ S → (∀ w ∈ W', ∀ s ∈ S, w * s = s * w) →
      (∀ b ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ w ∈ W', b * w * b⁻¹ ∈ W') →
      Nat.card W' = Nat.card W → W' = W₁ ∨ W' = W₂)
    (hWS : W ≤ S) (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w)
    (hBW : ∀ b ∈ L ⊓ Subgroup.normalizer (S : Set G), ∀ w ∈ W, b * w * b⁻¹ ∈ W) {g : G}
    (hgH : g ∈ H) (hgS : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  have hN : H ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    refine normalizes_of_odd_index hQ hQW (W₁ := W₁) (W₂ := W₂) fun g' hg' => ?_
    have hg'H : g' ∈ H := (Subgroup.mem_inf.1 hg').1
    have hg'S : g' ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.1 hg').2
    have hg'L := hHL hg'H
    have hinvS : g'⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hg'S
    have hinvL : g'⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hg'L
    refine hroots _ ?_ ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg'S w).1 (hWS hw)
    · rintro _ ⟨w, hw, rfl⟩ s hs
      have hs' : g'⁻¹ * s * g'⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hinvS s).1 hs
      have h1 := hWc w hw _ hs'
      show g' * w * g'⁻¹ * s = s * (g' * w * g'⁻¹)
      calc g' * w * g'⁻¹ * s = g' * (w * (g'⁻¹ * s * g')) * g'⁻¹ := by group
        _ = g' * ((g'⁻¹ * s * g') * w) * g'⁻¹ := by
          rw [show g'⁻¹ * s * g'⁻¹⁻¹ = g'⁻¹ * s * g' by group] at h1
          rw [h1]
        _ = s * (g' * w * g'⁻¹) := by group
    · rintro b hb _ ⟨w, hw, rfl⟩
      have hb' : g'⁻¹ * b * g'⁻¹⁻¹ ∈ L ⊓ Subgroup.normalizer (S : Set G) :=
        (Subgroup.mem_normalizer_iff.1 (mem_normalizer_inf_normalizer hinvL hinvS) b).1 hb
      have h1 := hBW _ hb' w hw
      refine ⟨_, h1, ?_⟩
      show g' * (g'⁻¹ * b * g'⁻¹⁻¹ * w * (g'⁻¹ * b * g'⁻¹⁻¹)⁻¹) * g'⁻¹ = b * (g' * w * g'⁻¹) * b⁻¹
      group
    · exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hgW : g ∈ Subgroup.normalizer (W : Set G) := hN (Subgroup.mem_inf.2 ⟨hgH, hgS⟩)
  have hgU : g ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_of_centralizes (hHU g hgH) (hHU g⁻¹ (H.inv_mem hgH))
  rw [← hsup]
  exact mem_normalizer_sup hgU hgW

end Main

end CFSG.Quasithin.RonanE611
