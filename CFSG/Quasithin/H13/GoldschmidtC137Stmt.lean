module

public import CFSG.Quasithin.H13.GoldschmidtC137Concl

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def C137StatementFiveSQTK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
    CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨ autOn T V ≤ autOn L V ∨
      ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
    (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      Nat.card ↥⁅V, L⁆ = 8 ∧ ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) →
    Concl X T V L P

theorem c137StatementFiveSQTK_of (h : C137StatementFive) : C137StatementFiveSQTK :=
  fun G _ _ X T V L P M hX _ => h G X T V L P M hX

@[expose] def C137SQTKSupply : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) → L ∈ cComp X →
    CharTwo L →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    SQTKGroup ↥X

theorem c137StatementFive_of_sqtk (h : C137StatementFiveSQTK) (hs : C137SQTKSupply) :
    C137StatementFive :=
  statement_of fun G _ _ X T V L P M hX hT hprod hL hL2 htype =>
    h G X T V L P M hX (hs G X T L hX hT hprod hL hL2 htype) hT hprod hL hL2 htype

end CFSG.Quasithin.H13.U3.GC137
