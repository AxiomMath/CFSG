module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory

@[expose] def KF1214ZRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L r → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      (∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) →
      (∀ z ∈ Subgroup.centralizer (I : Set G) ⊓ P, ∀ z' ∈ Subgroup.centralizer (I : Set G) ⊓ P,
        z * z' = z' * z) ∧
      Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) = Monoid.exponent ↥(P ⊓ I) ∧
      Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) =
        p * Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P ⊓ Subgroup.centralizer ({c} : Set G))

end CFSG.RankThree.PartOne.K1214
