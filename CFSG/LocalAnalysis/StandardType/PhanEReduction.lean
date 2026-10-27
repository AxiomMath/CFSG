module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

section Family

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

structure PhanFamilyE {n : ℕ} (M : CoxeterMatrix (Fin n)) (Y : Type) [Group Y] where
  ι : Fin n → (Su K p f 2 →* Y)
  θ : Fin n → Fin n → (Su K p f 3 →* Y)
  left : ∀ i j : Fin n, i < j → M i j = 3 →
    (θ i j).comp (embSUid (unitaryInvolution K p f) 2) = ι i
  right : ∀ i j : Fin n, i < j → M i j = 3 →
    (θ i j).comp (embSUid (unitaryInvolution K p f) 0) = ι j
  comm : ∀ i j : Fin n, M i j = 2 → ∀ a b, ι i a * ι j b = ι j b * ι i a

variable {K p f}

@[expose] def PhanFamilyE.IsUniversal {n : ℕ} {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
    (S : PhanFamilyE K p f M G) : Prop :=
  ∀ (Y : Type) [Group Y] (F : PhanFamilyE K p f M Y), ∃ ψ : G →* Y,
    (∀ i, ψ.comp (S.ι i) = F.ι i) ∧
      ∀ i j : Fin n, i < j → M i j = 3 → ψ.comp (S.θ i j) = F.θ i j

end Family

section Flip

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] (cs : CoxeterSystem M W)
  {C : Type} (δ : C → C → W)

structure IsSphericalFlip (w₀ : W) (t : C → C) : Prop where
  invol : ∀ x, t (t x) = x
  dist : ∀ x y, δ (t x) (t y) = w₀ * δ x y * w₀
  panel : ∀ (i : ι) (x : C), ∃ y ∈ residue cs δ {i} x, ∃ u ∈ residue cs δ {i} x,
    cs.length (δ u (t y)) < cs.length (δ y (t y))

@[expose] def flipMaxSet (t : C → C) (J : Set ι) (x : C) : Set C :=
  {y | y ∈ residue cs δ J x ∧
    ∀ z ∈ residue cs δ J x, cs.length (δ z (t z)) ≤ cs.length (δ y (t y))}

@[expose] def flipOpSet (w₀ : W) (t : C → C) : Set C := {c | δ c (t c) = w₀}

@[expose] def panelRel (i : ι) : C → C → Prop :=
  Relation.EqvGen fun a b => δ a b = cs.simple i

@[expose] def inducedSystem (J : Set ι) (A : Set C) : ChamberSystem J A where
  adj j y z := panelRel cs δ j y z
  equivalence _ := (Relation.EqvGen.is_equivalence _).comap _

@[expose] def inducedSystemAll (A : Set C) : ChamberSystem ι A where
  adj i y z := panelRel cs δ i y z
  equivalence _ := (Relation.EqvGen.is_equivalence _).comap _

end Flip

@[expose] def DM07Thm66 : Prop :=
  ∀ {ι : Type} [Finite ι] {M : CoxeterMatrix ι} {W : Type} [Group W] (cs : CoxeterSystem M W)
    (w₀ : W), (∀ w : W, cs.length (w * w₀) + cs.length w = cs.length w₀) →
    ∀ {C : Type} (δ : C → C → W), IsWeylDistanceBuilding cs δ →
    (∀ (i : ι) (x : C), ∃ y z : C, δ x y = cs.simple i ∧ δ x z = cs.simple i ∧ y ≠ z) →
    ∀ t : C → C, IsSphericalFlip cs δ w₀ t →
    (∀ (J : Set ι) (x : C), J.ncard = 2 →
      (inducedSystem cs δ J (flipMaxSet cs δ t J x)).Connected) →
    (∀ (J : Set ι) (x : C), J.ncard = 3 →
      (inducedSystem cs δ J (flipMaxSet cs δ t J x)).Connected ∧
        (inducedSystem cs δ J (flipMaxSet cs δ t J x)).SimplyTwoConnected) →
    (inducedSystemAll cs δ (flipOpSet δ w₀ t)).Connected ∧
      (inducedSystemAll cs δ (flipOpSet δ w₀ t)).SimplyTwoConnected

section Config

structure PhanEBuildingData {n : ℕ} (M : CoxeterMatrix (Fin n)) : Type 1 where
  w₀ : M.Group
  longest : ∀ w : M.Group,
    M.toCoxeterSystem.length (w * w₀) + M.toCoxeterSystem.length w = M.toCoxeterSystem.length w₀
  C : Type
  δ : C → C → M.Group
  building : IsWeylDistanceBuilding M.toCoxeterSystem δ
  thick : ∀ (i : Fin n) (x : C), ∃ y z : C,
    δ x y = M.toCoxeterSystem.simple i ∧ δ x z = M.toCoxeterSystem.simple i ∧ y ≠ z
  t : C → C
  flip : IsSphericalFlip M.toCoxeterSystem δ w₀ t

@[expose] def PhanEBuildingData.LocalConnected {n : ℕ} {M : CoxeterMatrix (Fin n)}
    (c : PhanEBuildingData M) : Prop :=
  (∀ (J : Set (Fin n)) (x : c.C), J.ncard = 2 →
    (inducedSystem M.toCoxeterSystem c.δ J (flipMaxSet M.toCoxeterSystem c.δ c.t J x)).Connected) ∧
  (∀ (J : Set (Fin n)) (x : c.C), J.ncard = 3 →
    (inducedSystem M.toCoxeterSystem c.δ J (flipMaxSet M.toCoxeterSystem c.δ c.t J x)).Connected ∧
      (inducedSystem M.toCoxeterSystem c.δ J
        (flipMaxSet M.toCoxeterSystem c.δ c.t J x)).SimplyTwoConnected)

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

structure PhanEConfig {n : ℕ} (M : CoxeterMatrix (Fin n)) (G : Type) [Group G] : Type 1
    extends PhanEBuildingData M where
  S : PhanFamilyE K 2 f M G

variable {K f}

@[expose] def PhanEConfig.ofData {n : ℕ} {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
    (bd : PhanEBuildingData M) (S : PhanFamilyE K 2 f M G) : PhanEConfig K f M G :=
  { bd with S := S }

@[expose] def PhanEConfig.Bridge {n : ℕ} {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
    (c : PhanEConfig K f M G) : Prop :=
  (inducedSystemAll M.toCoxeterSystem c.δ (flipOpSet c.δ c.w₀ c.t)).Connected →
    (inducedSystemAll M.toCoxeterSystem c.δ (flipOpSet c.δ c.w₀ c.t)).SimplyTwoConnected →
      c.S.IsUniversal

end Config

@[expose] def PhanELiftAt (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] {n : ℕ}
    (M : CoxeterMatrix (Fin n)) (Y : LieUniversal) : Prop :=
  (∃ S : PhanFamilyE K 2 f M Y.K, S.IsUniversal) →
    ∀ {X : Type} [Group X] (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X),
      WeakPhanSL K 2 f M U W → IsCentralQuotientOf Y X

theorem centralQuotient_of_config {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}
    {M : CoxeterMatrix (Fin n)} {Y : LieUniversal} (c : PhanEConfig K f M Y.K)
    (h1 : c.LocalConnected) (h2 : DM07Thm66) (h3 : c.Bridge) (h4 : PhanELiftAt K f M Y)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X)
    (hW : WeakPhanSL K 2 f M U W) : IsCentralQuotientOf Y X := by
  obtain ⟨hconn, hsc⟩ := h2 M.toCoxeterSystem c.w₀ c.longest c.δ c.building c.thick c.t c.flip
    h1.1 h1.2
  exact h4 ⟨c.S, h3 hconn hsc⟩ U W hW

structure PhanEConfigs (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] : Type 1 where
  e6 : PhanEConfig K f CoxeterMatrix.E₆ (lieUniversal .twistedE6 0 2 f Nat.prime_two).K
  e7 : PhanEConfig K f CoxeterMatrix.E₇ (lieUniversal .E7 0 2 f Nat.prime_two).K
  e8 : PhanEConfig K f CoxeterMatrix.E₈ (lieUniversal .E8 0 2 f Nat.prime_two).K

abbrev PhanEConfigChoice : Type 1 :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2],
    Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f → PhanEConfigs K f

@[expose] def PhanELocal (cfg : PhanEConfigChoice) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f),
    (cfg K f hK hq).e6.LocalConnected ∧ (cfg K f hK hq).e7.LocalConnected ∧
      (cfg K f hK hq).e8.LocalConnected

@[expose] def PhanEBridge (cfg : PhanEConfigChoice) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f),
    (cfg K f hK hq).e6.Bridge ∧ (cfg K f hK hq).e7.Bridge ∧ (cfg K f hK hq).e8.Bridge

@[expose] def PhanELift : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2], Nat.card K = (2 ^ f) ^ 2 → 4 ≤ 2 ^ f →
    PhanELiftAt K f CoxeterMatrix.E₆ (lieUniversal .twistedE6 0 2 f Nat.prime_two) ∧
      PhanELiftAt K f CoxeterMatrix.E₇ (lieUniversal .E7 0 2 f Nat.prime_two) ∧
      PhanELiftAt K f CoxeterMatrix.E₈ (lieUniversal .E8 0 2 f Nat.prime_two)

theorem phanEInput2_of_parts (cfg : PhanEConfigChoice) (h1 : PhanELocal cfg)
    (h2 : DM07Thm66) (h3 : PhanEBridge cfg) (h4 : PhanELift) : PhanEInput2 := by
  intro K _ _ f _ hK hq
  obtain ⟨l6, l7, l8⟩ := h1 K f hK hq
  obtain ⟨b6, b7, b8⟩ := h3 K f hK hq
  obtain ⟨f6, f7, f8⟩ := h4 K f hK hq
  exact ⟨fun U W hW => centralQuotient_of_config _ l6 h2 b6 f6 U W hW,
    fun U W hW => centralQuotient_of_config _ l7 h2 b7 f7 U W hW,
    fun U W hW => centralQuotient_of_config _ l8 h2 b8 f8 U W hW⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
