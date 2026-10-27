module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def W23_1 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) : Subgroup G :=
  conjClosure c.L0 D.Z

@[expose] def IsClassicalGroup23 (X : Type) [Group X] (n : ℕ) : Prop :=
  IsL2 X n ∨ IsOmegaMinus X 4 n ∨ IsOmegaPlus X 4 n ∨ IsSp4 X n ∨ IsSLn X 3 n ∨
    (∃ a : ℕ, n = 2 * a ∧ IsSUn X 4 a) ∨ IsOmegaMinus X 6 n ∨ IsSLn X 4 n ∨
    IsOmegaPlus X 6 n ∨ IsSpn X 6 n ∨ IsOmega8m X n

@[expose] def IsNaturalClassicalModule {W : Type} [CommGroup W]
    (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  (IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) ∨
    (IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) ∨
    (IsOmegaPlus ↥H 4 n ∧ NatOmegaPlus H ⊤ ⊥ 4 n) ∨
    (IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) ∨
    (IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) ∨
    (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) ∨
    (IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) ∨
    (IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) ∨
    (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) ∨
    (IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) ∨
    (IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n)

@[expose] def S23_2_natural (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∃ hV : IsElemAbelian 2 c.V, ∃ n : ℕ,
    Nat.card c.U0 = 2 ^ n ∧
      IsNaturalClassicalModule (barSub ⊥ c.V hV c.L) n

@[expose] def S23_3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, c.U0 = D.U

@[expose] def S23_4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch,
    D.U = D.Z ∧ D.U ≤ D.M ∧ D.M ≤ normalizer (D.U : Set G)

@[expose] def X23_4 (D : Data G) (N₁ : Subgroup G) : Subgroup G :=
  ⨆ L ∈ calLOf D.T D.M N₁, L

end CFSG.LocalAnalysis.UniquenessCase.UC22
