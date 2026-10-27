module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.F9Dihedral

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L2OddInnerFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), LieModel X .PSL 2 2 n → Odd n →
    ∀ φ : MulAut X, (∃ k : ℕ, φ ^ 2 ^ k = 1) → ∃ x : X, φ = MulAut.conj x

@[expose] def L34SylowNormFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ φ : MulAut X, S.map φ.toMonoidHom = S →
      Nat.Coprime (orderOf φ) 6 → φ = 1

end CFSG.Quasithin.H13
