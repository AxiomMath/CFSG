module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCD

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGIsF4Matrix {Λ : Type} (M : CoxeterMatrix Λ) : Prop :=
  ∃ e : Fin 4 ≃ Λ, ∀ i j, M (e i) (e j) = CoxeterMatrix.F₄ i j

@[expose] def GGForkF1Fails {Λ : Type} [Fintype Λ] (M : CoxeterMatrix Λ) : Prop :=
  (Fintype.card Λ = 3 ∧ ∃ i j, M i j = 4) ∨ GGIsF4Matrix M

@[expose] def GGForkCrossGe5MainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
        ∀ [Fact p.Prime], 5 ≤ p →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      ¬ GGForkF1Fails M → 3 ≤ Fintype.card Λ → αa (h b) = 0 ∨ αa (h b) = 1

@[expose] def GGForkCrossGe5ExcInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
        ∀ [Fact p.Prime], 5 ≤ p →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      GGForkF1Fails M → αa (h b) = 0 ∨ αa (h b) = 1

section Cells

variable {Λ : Type} [DecidableEq Λ]

@[expose] def GGAttachWeyl (C : Matrix Λ Λ ℤ) (k : Λ) : Prop :=
  ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧ GGIntCartan M' (ggAttachCartan C k)

@[expose] def GGAttachNullPos [Fintype Λ] (C : Matrix Λ Λ ℤ) (k : Λ) : Prop :=
  ∃ n : Option Λ → ℕ, (∀ i, 0 < n i) ∧ ∀ i, ∑ j, (n j : ℤ) * ggAttachCartan C k j i = 0

end Cells

@[expose] def GGForkAffineExclRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      ¬ GGForkShapeA C b → ¬ GGForkShapeBCD C b →
      (αa (h b) = 0 → ¬ GGAttachNullPos C c) ∧ (αa (h b) = 1 → ¬ GGAttachNullPos C b)

@[expose] def GGForkIndefExclRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      ¬ GGForkShapeA C b → ¬ GGForkShapeBCD C b →
      (αa (h b) = 0 → GGAttachWeyl C c ∨ GGAttachNullPos C c) ∧
        (αa (h b) = 1 → GGAttachWeyl C b ∨ GGAttachNullPos C b)

end CFSG.StandardType
