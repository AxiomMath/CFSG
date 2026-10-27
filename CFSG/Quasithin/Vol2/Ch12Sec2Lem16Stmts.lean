module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Orbit

@[expose] def OrbitL32Four : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 4 →
    ∀ H : Subgroup (MulAut V), Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      commV H = ⊤ →
      (∀ W : Subgroup V, fixV H ≤ W → (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) →
        W = fixV H ∨ W = ⊤) →
      (∀ A B : Subgroup V, (∀ h ∈ H, ∀ a ∈ A, (h : MulAut V) a ∈ A) →
        (∀ h ∈ H, ∀ b ∈ B, (h : MulAut V) b ∈ B) → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) →
        OrbitLengthsIn H [1, 14] ∧ OrbitsSeparated H

@[expose] def CoreSixTwoCentral : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X S : Subgroup (MulAut V)) (z : V), z ≠ 1 →
    z ∈ fixV H → (altCoreModel 6).Realizes H ⊤ ⊥ → H ≤ X →
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsSylowTwoOf S X →
      ∀ v : V, v ≠ 1 → v ≠ z → ∃ x ∈ X, ∀ s ∈ S, (s : MulAut V) (x v) = x v

@[expose] def G2WeylTwoCentral : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X S : Subgroup (MulAut V)) (z : V), z ≠ 1 →
    z ∈ fixV H → G2WeylDerived H → H ≤ X → X ≤ Subgroup.normalizer (H : Set (MulAut V)) →
    IsSylowTwoOf S X → ∀ v : V, v ≠ 1 → v ≠ z → ∃ x ∈ X, ∀ s ∈ S, (s : MulAut V) (x v) = x v

@[expose] def Lem12216CoreEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z v g : G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
    (∃ _ : IsMulCommutative ↥V, (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥) →
    V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z → z ≠ 1 →
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) →
    v ∈ V → v ∉ Subgroup.zpowers z → g ∉ Subgroup.normalizer (L : Set G) →
    g⁻¹ * v * g = v * z →
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G)) (Subgroup.centralizer ({v} : Set G)) →
    g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) →
      False

end CFSG.Quasithin.H13
