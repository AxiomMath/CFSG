module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def IsCentralL3Sp4 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 3 2 n (X ⧸ Subgroup.center X) ∨ IsPSp4 2 n (X ⧸ Subgroup.center X)

structure ShapeL3Sp4 (T K1 K : Subgroup G) : Prop where
  exists_n : ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (OTwoQuot K1) ∧ IsCentralL3Sp4 n (OTwoQuot K)
  diag : E2.IsDiagramNontrivial T K (T ⊓ K)
  parabolic : ∃ P P' : Subgroup G, P ≠ P' ∧ IsMaxParabolic2 K P ∧ IsMaxParabolic2 K P' ∧
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P ⊓ P' ∧ K1 = perfectCore P ∧
    ∀ A : Subgroup G, T ⊓ K ≤ A → A ≤ K → (A ⋖ K ↔ A = P ∨ A = P')

structure Shape1428 (T H K1 : Subgroup G) : Prop where
  cases : (K1 = oTwoUpper H ∧ oTwoUpper H ∈ cComp H) ∨
    (K1 ∈ cComp H ∧ K1 < oTwoUpper H) ∨
    (oTwoUpper H ∈ cComp H ∧ K1 < oTwoUpper H ∧ ShapeL3Sp4 T K1 (oTwoUpper H))

end CFSG.Quasithin
