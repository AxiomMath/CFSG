module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Walter

open scoped MatrixGroups

@[expose] def HasAbelianSylowTwo (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)

@[expose] def IsTypeL2 (L : Type*) [Group L] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))) ∨
  (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f)))

@[expose] def IsTypeJR (G : Type*) [Group G] : Prop :=
  IsSimpleGroup G ∧ HasAbelianSylowTwo G ∧
    ∀ t : G, orderOf t = 2 →
      IsCoatom (Subgroup.centralizer ({t} : Set G)) ∧
      ∃ (p f : ℕ) (_hp : Fact p.Prime) (L : Subgroup G), Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        L ≤ Subgroup.centralizer ({t} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal ∧
        Nonempty (L ≃* PSL(2, GaloisField p f)) ∧
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
          Subgroup.zpowers t

@[expose] def IsAStar (X : Type*) [Group X] : Prop :=
  HasAbelianSylowTwo X ∧
    Odd (GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))).index ∧
    ∀ K : Subgroup (X ⧸ pPrimeCore 2 X), GorensteinWalter.IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ ∧ (IsTypeL2 K ∨ IsTypeJR K)

end CFSG.Walter
