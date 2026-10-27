module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Apart

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF4k_PolyArcs : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ), 2 ≤ m →
    UniqueGeod c.graph m →
    ∀ (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * m) = z i) → ∀ i : ℕ,
        GPath.arc₁ z hz m i ∈ c.geods m (z i) (z (i + m)) ∧
        GPath.arc₂ z hz m i ∈ c.geods m (z i) (z (i + m)) ∧
        GPath.arc₁ z hz m i ≠ GPath.arc₂ z hz m i ∧
        Set.range z = (GPath.arc₁ z hz m i).verts ∪ (GPath.arc₂ z hz m i).verts

@[expose] def burnsideF4k_PolyRefl : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ), 2 ≤ m →
    UniqueGeod c.graph m →
    ∀ (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * m) = z i) → ∀ (i : ℕ) (g : c.G0),
        g • GPath.arc₁ z hz m i = GPath.arc₂ z hz m i →
        g • GPath.arc₂ z hz m i = GPath.arc₁ z hz m i →
        IsReflectionOn c g (Set.range z) (z i)

@[expose] def burnsideF4k_PolyW : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ), 2 ≤ m →
    UniqueGeod c.graph m →
    ∀ (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * m) = z i) → z 0 = c.xv → z 1 = c.lv → ∀ sx sl : c.G0,
        sx • GPath.arc₁ z hz m 0 = GPath.arc₂ z hz m 0 →
        sx • GPath.arc₂ z hz m 0 = GPath.arc₁ z hz m 0 →
        sl • GPath.arc₁ z hz m 1 = GPath.arc₂ z hz m 1 →
        sl • GPath.arc₂ z hz m 1 = GPath.arc₁ z hz m 1 →
        IsF415W c m (Set.range z) sx sl ∧
          ((pointwiseStab c (Set.range z)).subgroupOf (setStab c (Set.range z))).index = 2 * m

@[expose] def burnsideF4k_PolyOpp : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ), 2 ≤ m →
    UniqueGeod c.graph m →
    ∀ (z : ℕ → c.Γ), (∀ i, c.graph.Adj (z i) (z (i + 1))) → (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * m) = z i) → ∀ i j : ℕ, c.graph.dist (z i) (z j) = m → z j = z (i + m)

@[expose] def burnsideF4k_PolyNbr : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ), 2 ≤ m →
    UniqueGeod c.graph m →
    ∀ (z : ℕ → c.Γ), (∀ i, c.graph.Adj (z i) (z (i + 1))) → (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * m) = z i) → ∀ (i : ℕ) (w : c.Γ), w ∈ Set.range z →
        c.graph.Adj (z i) w → w = z (i + 1) ∨ w = z (i + 2 * m - 1)

@[expose] def burnsideF4k_PolyG2d : Prop :=
  ∀ {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z),
    UniqueGeod c.graph 6 →
    ∀ (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) →
      (∀ i, z (i + 2 * 6) = z i) → z 0 = c.xv → z 1 = c.lv → ∀ sl sc : c.G0,
        sl • GPath.arc₁ z hz 6 1 = GPath.arc₂ z hz 6 1 →
        sl • GPath.arc₂ z hz 6 1 = GPath.arc₁ z hz 6 1 →
        sc • GPath.arc₁ z hz 6 11 = GPath.arc₂ z hz 6 11 →
        sc • GPath.arc₂ z hz 6 11 = GPath.arc₁ z hz 6 11 →
        (∀ g ∈ setStab c (Set.range z), g • z 0 = z 0 → g = 1) →
          setStab c (Set.range z) = Subgroup.closure {sl, sc} ∧
          Nonempty (↥(setStab c (Set.range z)) ≃* Equiv.Perm (Fin 3)) ∧
          Set.ncard {u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = false} = 6 ∧
          (∀ u ∈ Set.range z, CosetGeom.vtype u = false → ∀ v ∈ Set.range z,
            CosetGeom.vtype v = false → ∃! w : ↥(setStab c (Set.range z)), (w : c.G0) • u = v) ∧
          {u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = true} =
            {u | ∃ w ∈ setStab c (Set.range z), w • c.lv = u} ∪
              {u | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} ∧
          Disjoint {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • c.lv = u}
            {u | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} ∧
          Set.ncard {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • c.lv = u} = 3 ∧
          Set.ncard {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} = 3

@[expose] def burnsideF4k_GrpD10 : Prop :=
  ∀ {G X : Type} [Group G] [MulAction G X] (H : Subgroup G), Nonempty (↥H ≃* DihedralGroup 5) →
    ∀ Λ : Set X, (∀ h ∈ H, ∀ r ∈ Λ, h • r ∈ Λ) → (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ h ∈ H, h • r₁ = r₂) →
      Nat.card ↥Λ = 5 →
      (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∃ h ∈ H, h • r₁ = r₂ ∧ h • r₂ = r₁) ∧
      (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∀ h ∈ H, h • r₁ = r₁ → h • r₂ = r₂ → h = 1)

@[expose] def burnsideF4k_GrpZ3 : Prop :=
  ∀ {G X : Type} [Group G] [MulAction G X] (H : Subgroup G),
    Nonempty (↥H ≃* Multiplicative (ZMod 3)) →
    ∀ Λ : Set X, (∀ h ∈ H, ∀ r ∈ Λ, h • r ∈ Λ) → (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ h ∈ H, h • r₁ = r₂) →
      Nat.card ↥Λ = 3 →
      (∀ r ∈ Λ, ∀ h ∈ H, h • r = r → h = 1) ∧
      (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∀ h ∈ H, h • r₁ = r₂ → h • r₂ = r₁ → False)

@[expose] def burnsideF4k_GrpTwoTrans : Prop :=
  ∀ {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) (Λ : Set X), Finite ↥H → Λ.Finite →
    2 ≤ Nat.card ↥Λ → (∀ h ∈ H, ∀ r ∈ Λ, h • r ∈ Λ) →
    (∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, r₁ ≠ r₂ → ∀ s₁ ∈ Λ, ∀ s₂ ∈ Λ, s₁ ≠ s₂ →
      ∃ h ∈ H, h • r₁ = s₁ ∧ h • r₂ = s₂) →
    Nat.card ↥Λ * (Nat.card ↥Λ - 1) ∣ Nat.card ↥H

end CFSG.ASVolI
