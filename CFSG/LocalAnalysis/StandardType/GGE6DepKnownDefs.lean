module

public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section KnownGroup

@[expose] def GGE6DepBlocks (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
    (∀ φ ∈ ggTorusAut A, ¬ GGIsTransvection 3 φ) →
    (∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c → ∀ P : Subgroup L',
        P ≤ ggFix (c : MulAut L') → ⁅P, P⁆ = P →
          P ≤ ⨆ (J : Subgroup L') (_ : IsComponentOf J (ggFix (c : MulAut L'))), J) ∧
    ∀ a b : ↥A, GGCorootOrth 3 (ggTorusAut A) a b →
      ∃ Dv N : Subgroup L',
        IsComponentOf Dv (ggFix ((a : MulAut L') * (b : MulAut L'))) ∧
        (∀ J : Subgroup L', IsComponentOf J (ggFix ((a : MulAut L') * (b : MulAut L'))) → J = Dv) ∧
        IsComponentOf N (ggFix (a : MulAut L') ⊓ ggFix (b : MulAut L')) ∧
        (∀ J : Subgroup L', IsComponentOf J (ggFix (a : MulAut L') ⊓ ggFix (b : MulAut L')) →
          J = N) ∧
        N ≤ Dv ∧ IsCyclic (Subgroup.center N) ∧
        3 ^ 3 ≤ Nat.card ↥(ggFixedByCentres 3 (ggTorusAut A) {a, b}) ∧
        (∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
          ∃ n ∈ N, MulAut.conj n = (u : MulAut L')) ∧
        ∃ n ∈ Dv, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
          MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ ≠ (a : MulAut L')

@[expose] def GGE6DepBlockKnown : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6DepBlocks R I

end KnownGroup

section Setting

variable {G : Type} [Group G] [Finite G]

@[expose] def GGE6DepConjSetting (p : ℕ) (Bs : Subgroup G) (x y : G) (L : Subgroup G) : Prop :=
  ¬ p ∣ Nat.card ↥(Subgroup.center ↥L) ∧ (∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) ∧
  ∃ (g x₁ y₁ w : G) (hx₁ : x₁ ∈ Bs) (hy₁ : y₁ ∈ Bs) (hy : y ∈ Bs) (hw : w ∈ Bs),
    g ∈ Subgroup.normalizer (Bs : Set G) ∧ x = g * x₁ * g⁻¹ ∧ y = g * y₁ * g⁻¹ ∧
    w = g * x * g⁻¹ ∧ x₁ ∈ L ∧ y₁ ∈ L ∧ y ∈ L ∧ w ∈ L ∧
    GGCorootOrth p (ggAutomizer L Bs) ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩ ∧
    GGCorootOrth p (ggAutomizer L Bs) ⟨y, hy⟩ ⟨w, hw⟩ ∧
    ∃ U : Subgroup ↥Bs, 3 ^ 3 ≤ Nat.card U ∧
      U ≤ ggFixedByCentres p (ggAutomizer L Bs) {⟨y, hy⟩, ⟨w, hw⟩} ∧
      ∀ u ∈ U, (u : G) ∈ L ∧
        ∃ u₁ ∈ ggFixedByCentres p (ggAutomizer L Bs) {⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩},
          (u₁ : G) ∈ L ∧ (u₁ : G) = g⁻¹ * u * g

@[expose] def GGE6DepConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K → GGE6DepConjSetting p Bs x y L

end Setting

end CFSG.StandardType

end
