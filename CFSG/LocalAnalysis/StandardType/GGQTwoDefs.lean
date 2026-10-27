module

public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQTwoSetting {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGCorFiveTwentyHyp p B Bs x L D J ∧ GGInnerDiagOnLabel GGLabQTwo p Bs L ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ¬ GGE6DepPerpCfg p Bs L K

@[expose] def ggReflGp {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) : Subgroup (MulAut ↥Bs) :=
  Subgroup.closure {φ | φ ∈ ggAutomizer ⊤ Bs ∧ GGIsReflection p φ}

@[expose] def GGGammaAt {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (u : ↥Bs) : Prop :=
  ∀ φ ∈ ggAutomizer ⊤ Bs, φ u ∈ Subgroup.zpowers u →
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

@[expose] def GGOrbitStableAt {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (u : ↥Bs) : Prop :=
  ∀ φ ∈ ggAutomizer ⊤ Bs, ∃ r ∈ ggReflGp p Bs,
    Subgroup.zpowers (φ u) = Subgroup.zpowers (r u)

@[expose] def GGLemmaXCond {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  ∀ φ ∈ ggAutomizer ⊤ Bs, ∀ u : ↥Bs,
    ((u : G) = x ∨ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ (u : G) = y) →
      ∃ r ∈ ggReflGp p Bs, ∃ w : ↥Bs, (w : G) ∈ D ∧ w ≠ 1 ∧
        Subgroup.zpowers (φ u) = Subgroup.zpowers (r w)

@[expose] def GGNbrLine {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (D J : Subgroup G) {Bs : Subgroup G} (u : ↥Bs) : Prop :=
  ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
    Subgroup.zpowers y = Subgroup.zpowers (u : G)

@[expose] def GGTrivialLine {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (D J : Subgroup G) {Bs : Subgroup G} (u : ↥Bs) : Prop :=
  Subgroup.zpowers (u : G) ≠ Subgroup.zpowers x ∧ ¬ GGNbrLine p B x D J u

@[expose] def GGQ2Orbit {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  (∃ u : ↥Bs, (u : G) ∈ D ∧ u ≠ 1 ∧ GGOrbitStableAt p Bs u) ∨ GGLemmaXCond p B Bs x D J

end CFSG.StandardType

end
