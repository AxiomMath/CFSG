module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGResExactTwoOrthFixOmega : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 →
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate → 8 ≤ Module.finrank F V →
    ∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
      (∀ g : ↥(CFSG.RankThree.Classical2.orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 →
        g ∈ E) →
    ∀ t ∈ E, t ≠ 1 → ∀ C : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q),
      IsComponentOf C
        (Subgroup.centralizer ({t} : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) →
    ∀ e ∈ E, (∀ n ∈ C, (∀ a ∈ E, n * a * n⁻¹ ∈ E) → n * e = e * n) →
      e ∈ Subgroup.centralizer (C : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))

@[expose] def GGResExactTwoOrthFormsOmega : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 →
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    (Module.finrank F V = 8 ∨ Module.finrank F V = 10) →
    OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] →
    ∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
      (∀ g : ↥(CFSG.RankThree.Classical2.orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 →
        g ∈ E) →
    ∀ t ∈ E, t ≠ 1 → ∀ C : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q),
      IsComponentOf C
        (Subgroup.centralizer ({t} : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) →
      9 ≤ Nat.card
        ↥(E ⊓ Subgroup.centralizer (C : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) →
      Module.finrank F V = 10 ∧ LargeEvenIsU42 ↥C

@[expose] def GGResExactTwoOrthFixLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧
      4 ≤ lab.rank) p Bs L →
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) → (b : G) ∈ Subgroup.centralizer (J : Set G)

@[expose] def GGResExactTwoOrthDFourLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .D ∧ lab.n = 1 ∧ lab.rank = 4) p Bs L →
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 9

@[expose] def GGResExactTwoOrthTwDFiveLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .twD ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L →
    27 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) → LargeEvenSmall J

@[expose] def GGResExactTwoOrthSelLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .twD ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L →
    B ≠ Bs → ∃ D₁ K₁ : Subgroup G, LargeEvenStdSubPre p B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁

end CFSG.StandardType
