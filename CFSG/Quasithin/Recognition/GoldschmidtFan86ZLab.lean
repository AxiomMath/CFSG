module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V : Type*} (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]

@[expose] def IsCentralInvolIn (v : V) (z : G) : Prop :=
  z ∈ MulAction.stabilizer G v ∧ z ≠ 1 ∧ z * z = 1 ∧
    ∀ g ∈ MulAction.stabilizer G v, g * z = z * g

structure ZLab where
  z : V → G
  isCentral : ∀ v, valence Γ v = 5 → IsCentralInvolIn G v (z v)
  equivariant : ∀ (g : G) (v : V), valence Γ v = 5 → z (g • v) = g * z v * g⁻¹

variable {Γ G}

@[expose] def ZLab.Unique (L : ZLab Γ G) : Prop :=
  ∀ v, valence Γ v = 5 → ∀ w, IsCentralInvolIn G v w → w = L.z v

@[expose] def fixedPts (g : G) : Set V := {v | g • v = v}

@[expose] def ZLab.zSet (L : ZLab Γ G) (k : ℕ) (α : V) : Set G :=
  {g | ∃ δ, Γ.dist α δ ≤ k ∧ valence Γ δ = 5 ∧ g = L.z δ}

@[expose] def ZLab.zGroup (L : ZLab Γ G) (k : ℕ) (α : V) : Subgroup G :=
  Subgroup.closure (L.zSet k α)

theorem ZLab.z_mem_zSet (L : ZLab Γ G) {k : ℕ} {α δ : V} (h : Γ.dist α δ ≤ k)
    (hδ : valence Γ δ = 5) : L.z δ ∈ L.zSet k α := ⟨δ, h, hδ, rfl⟩

end CFSG.Quasithin.Fan86
