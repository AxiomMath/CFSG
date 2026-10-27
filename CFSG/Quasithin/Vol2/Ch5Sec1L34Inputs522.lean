module

public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def Stmt5_1_22_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
      ((T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Subgroup G) : Set G) *
          (B : Set G) = (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Set G) ∧
        Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M

@[expose] def OrthKernelFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V S Dm : Subgroup G) (m : ℕ),
    IsOrthCh5 L V (2 * m) → IsSylowTwoOf S L →
    Dm ≤ L ⊓ Subgroup.normalizer (S : Set G) → Nat.card Dm = 2 ^ m + 1 →
      V ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer (Dm : Set G)

@[expose] def L34BorelFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 → ∀ S Y : Subgroup X,
    IsSylowTwoOf S ⊤ → Y ≤ Subgroup.normalizer (S : Set X) → Odd (Nat.card Y) →
      Nat.card Y ∣ 3

end CFSG.Quasithin.H13
