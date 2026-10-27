module

public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGForkCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl
public import CFSG.LocalAnalysis.StandardType.GGLatticeRootsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ConfigInputs

variable {G : Type} [Group G]

@[expose] def GGAutLattice (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥Bs), GGLatForm Q ∧
    (∀ b : ↥Bs, ∃ y : Fin m → ℤ,
      ((Additive.toMul (π y) : ↥Bs) : G)⁻¹ * (b : G) ∈ Subgroup.centralizer (X : Set G)) ∧
    ∀ t ∈ ggInduced X Bs, GGIsReflection p t → ∃ w : Fin m → ℤ, GGLatRoot Q w ∧
      ∀ y : Fin m → ℤ, ((t (Additive.toMul (π y)) : ↥Bs) : G)⁻¹ *
        ((Additive.toMul (π (ggLatRefl Q w y)) : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G)

end ConfigInputs

@[expose] def GGForkJr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → 5 ≤ p →
      ∀ r ∈ ggInduced L Bs, GGIsReflection p r →
        (∃ Jr : Subgroup G, r ∈ ggInduced Jr Bs ∧
          Jr ≤ Subgroup.centralizer (ggFixG Bs r : Set G) ∧
          IsPComponent p (Jr.subgroupOf (Subgroup.centralizer (ggFixG Bs r : Set G)))) ∧
        (D ≤ ggFixG Bs r → r ∈ ggInduced J Bs)

@[expose] def GGForkPump : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGScalarsPmOne Bs → 5 ≤ p →
        GGAutLattice p Bs L ∧
          ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            GGAutLattice p Bs K ∨ ∀ t ∈ ggInduced K Bs, ¬ GGIsReflection p t

@[expose] def GGForkPump' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGSecFiveWeylCase' p B Bs x D J → 5 ≤ p →
        GGAutLattice p Bs L ∧
          ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            GGAutLattice p Bs K ∨ ∀ t ∈ ggInduced K Bs, ¬ GGIsReflection p t

@[expose] def GGForkPumpOr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGScalarsOrWeyl' p B Bs x D J → 5 ≤ p →
        GGAutLattice p Bs L ∧
          ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
            GGAutLattice p Bs K ∨ ∀ t ∈ ggInduced K Bs, ¬ GGIsReflection p t

section TorusForms

variable (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R))

@[expose] def GGTorusRootSL2 : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
          (J : Subgroup L'), GGTorusWeylElt p A n ∧ ggConjAut A hn = φ ∧ n ∈ J ∧
          IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J ∧
          ∀ (a : MulAut L') (ha : a ∈ A), φ ⟨a, ha⟩ = ⟨a, ha⟩ → n ∈ LargeEvenLayer (ggFix a)

@[expose] def GGTorusLattice : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥A),
        GGLatForm Q ∧ Function.Surjective π ∧
        ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
          ∃ w : Fin m → ℤ, GGLatRoot Q w ∧
            ∀ y : Fin m → ℤ, φ (Additive.toMul (π y)) = Additive.toMul (π (ggLatRefl Q w y))

@[expose] def GGTorusNoRefl : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ¬ GGIsReflection p φ

end TorusForms

@[expose] def GGForkRootSL2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  5 ≤ p ∧ LargeEvenSplit p lab

@[expose] def GGForkLatticeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  5 ≤ p ∧ 2 ≤ lab.n ∧ p ∣ 4 ^ lab.n - 1

@[expose] def GGForkRootSL2KGInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGForkRootSL2Label p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I

@[expose] def GGForkLatticeKGInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGForkLatticeLabel p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I

@[expose] def GGForkE6TwoNoReflKGInput : Prop :=
  LargeEvenLabelAll ⟨.E6, 0, 1⟩ fun R _ I _ => ∃ r, GGTorusLift 7 r R ∧ GGTorusNoRefl 7 r R I

@[expose] def GGForkNbrSevenExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 7 B Bs x L D J → GGOpAutTrivial 7 Bs → GGInnerDiagAll 7 B Bs x L D J →
      GGNoTransvection 7 Bs → GGScalarsPmOne Bs →
      ∀ (y : G) (K : Subgroup G), GGNbr 7 B x D J y K →
        ¬ GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K)

@[expose] def GGForkE6TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 7 ∧ lab = ⟨.E6, 0, 1⟩

end CFSG.StandardType
