module

public import CFSG.Monster.B.Geometry.UnitaryExtension
public import CFSG.Monster.B.Geometry.OrthExtension

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.LieType.Chevalley.C2E6Overlap (K)

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)
  {C C' : Type*} (δ : C → C → W) (δ' : C' → C' → W)

@[expose] def FoundationExtension : Prop :=
  Rig₂ cs δ ∧ Rig₂ cs δ' ∧
    ∀ (c d : C) (c' d' : C'), δ c d = longest cs Set.univ → δ' c' d' = longest cs Set.univ →
      ∀ φ : C → C', IsWeylIsometry δ δ' (foundation cs δ 2 c ∪ {d})
          (foundation cs δ' 2 c' ∪ {d'}) φ → φ c = c' → φ d = d' →
        ∃ F : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F ∧
          Set.EqOn F φ (foundation cs δ 2 c ∪ {d}) ∧
          ∀ F' : C → C', IsTypeIso cs δ δ' Set.univ Set.univ F' →
            Set.EqOn F' φ (foundation cs δ 2 c ∪ {d}) → F' = F

theorem classical_rank_three_opposite_foundation_extension [Finite W]
    (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ') :
    (∀ u t s : ι, u ≠ t → t ≠ s → u ≠ s → (∀ i, i = u ∨ i = t ∨ i = s) →
      M u t = 3 → M t s = 4 → M u s = 2 →
      ∀ (f : C → PFlag UData) (f' : C' → PFlag UData),
        IsChamberModel cs δ (polarChamber UData u t s) f →
        IsChamberModel cs δ' (polarChamber UData u t s) f' → FoundationExtension cs δ δ') ∧
    (∀ s t u : ι, s ≠ t → t ≠ u → s ≠ u → (∀ i, i = s ∨ i = t ∨ i = u) →
      M s t = 3 → M t u = 4 → M s u = 2 →
      ∀ (f : C → PFlag OData) (f' : C' → PFlag OData),
        IsChamberModel cs δ (polarChamber OData s t u) f →
        IsChamberModel cs δ' (polarChamber OData s t u) f' → FoundationExtension cs δ δ') ∧
    (∀ a b z : ι, a ≠ b → a ≠ z → b ≠ z → (∀ i, i = a ∨ i = b ∨ i = z) →
      M a b = 3 → M a z = 2 → M b z = 2 →
      ∀ (f : C → PlaneFlag K × Fin 3) (f' : C' → PlaneFlag K × Fin 3),
        IsChamberModel cs δ (planeProduct K (Fin 3) a b z) f →
        IsChamberModel cs δ' (planeProduct K (Fin 3) a b z) f' → FoundationExtension cs δ δ') ∧
    (∀ a b z : ι, a ≠ b → a ≠ z → b ≠ z → (∀ i, i = a ∨ i = b ∨ i = z) →
      M a b = 3 → M a z = 2 → M b z = 2 →
      ∀ (f : C → PlaneFlag (ZMod 2) × Fin 5) (f' : C' → PlaneFlag (ZMod 2) × Fin 5),
        IsChamberModel cs δ (planeProduct (ZMod 2) (Fin 5) a b z) f →
        IsChamberModel cs δ' (planeProduct (ZMod 2) (Fin 5) a b z) f' →
          FoundationExtension cs δ δ') ∧
    (∀ u t s : ι, u ≠ t → t ≠ s → u ≠ s → (∀ i, i = u ∨ i = t ∨ i = s) →
      M u t = 3 → M t s = 4 → M u s = 2 →
      ∀ (f : C → PFlag UData) (hf : IsChamberModel cs δ (polarChamber UData u t s) f)
        (c₀ d₀ : C), f c₀ = uC0 → f d₀ = uD0 →
        (∀ (a : Fin 3 → Kˣ) (σ : K ≃+* K), hf.perm (uDiagPerm a σ) ∈ typeAut cs δ ∧
          hf.perm (uDiagPerm a σ) c₀ = c₀ ∧ hf.perm (uDiagPerm a σ) d₀ = d₀) ∧
        (∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ → ∃ (a : Fin 3 → Kˣ) (σ : K ≃+* K),
          Set.EqOn g (hf.perm (uDiagPerm a σ)) (foundation cs δ 2 c₀)) ∧
        (∀ (a a' : Fin 3 → Kˣ) (σ σ' : K ≃+* K),
          Set.EqOn (hf.perm (uDiagPerm a σ)) (hf.perm (uDiagPerm a' σ'))
            (foundation cs δ 2 c₀) ↔ σ = σ' ∧ ∃ r : Kˣ, ∀ i, a' i = r * a i) ∧
        Nat.card {φ : foundation cs δ 2 c₀ → C //
          ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x} = 18) ∧
    (∀ s t u : ι, s ≠ t → t ≠ u → s ≠ u → (∀ i, i = s ∨ i = t ∨ i = u) →
      M s t = 3 → M t u = 4 → M s u = 2 →
      ∀ (f : C → PFlag OData) (hf : IsChamberModel cs δ (polarChamber OData s t u) f)
        (c₀ d₀ : C), f c₀ = oC0 → f d₀ = oD0 →
        (∀ A : GL (Fin 2) (ZMod 2), hf.perm (oTailPerm A) ∈ typeAut cs δ ∧
          hf.perm (oTailPerm A) c₀ = c₀ ∧ hf.perm (oTailPerm A) d₀ = d₀) ∧
        (∀ g ∈ typeAut cs δ, g c₀ = c₀ → g d₀ = d₀ → ∃ A : GL (Fin 2) (ZMod 2),
          Set.EqOn g (hf.perm (oTailPerm A)) (foundation cs δ 2 c₀)) ∧
        (∀ A B : GL (Fin 2) (ZMod 2), Set.EqOn (hf.perm (oTailPerm A)) (hf.perm (oTailPerm B))
          (foundation cs δ 2 c₀) → A = B) ∧
        Nat.card {φ : foundation cs δ 2 c₀ → C //
          ∃ g ∈ typeAut cs δ, g c₀ = c₀ ∧ g d₀ = d₀ ∧ ∀ x, φ x = g x} = 6) := by
  refine ⟨fun u t s hut hts hus hι h1 h2 h3 f f' hf hf' =>
      unitary_extension hδ hδ' hut hts hus hι h1 h2 h3 hf hf',
    fun s t u hst htu hsu hι h1 h2 h3 f f' hf hf' =>
      orth_extension hδ hδ' hst htu hsu hι h1 h2 h3 hf hf',
    fun a b z hab haz hbz hι h1 h2 h3 f f' hf hf' =>
      planeProduct_extension hδ hδ' hab haz hbz hι h1 h2 h3 hf hf',
    fun a b z hab haz hbz hι h1 h2 h3 f f' hf hf' =>
      planeProduct_extension hδ hδ' hab haz hbz hι h1 h2 h3 hf hf',
    fun u t s hut hts hus hι h1 h2 h3 f hf c₀ d₀ hc₀ hd₀ =>
      unitary_stabilizer hδ hut hts hus hι h1 h2 h3 hf hc₀ hd₀,
    fun s t u hst htu hsu hι h1 h2 h3 f hf c₀ d₀ hc₀ hd₀ =>
      orth_stabilizer hδ hst htu hsu hι h1 h2 h3 hf hc₀ hd₀⟩

end CFSG.Monster.B.Geometry
