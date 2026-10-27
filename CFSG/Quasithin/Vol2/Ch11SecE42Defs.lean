module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

abbrev kz (L V₁ : Subgroup G) (z : G) : Subgroup G := KOf L V₁ (Subgroup.zpowers z)

@[expose] def IsSL2pE (X : Type) [Group X] : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
    CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
    IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X) ∧
    NaturalSL2Action p X (CFSG.fittingSubgroup X)

structure Conf11_4_2 [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (z : G) :
    Prop where
  hyp : Hyp11 G T L I n
  vi : IsVi T L I n 1 V₁
  mem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)
  ne_one : z ≠ 1
  lt : KOf L V₁ V₁ < kz L V₁ z
  list : List11_1_1Two (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) n ∨
    (n = 2 ∧ List11_1_1Three (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)))
  not_a36 : ¬ A36Case4 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z))
  not_sl2pE : ¬ IsSL2pE (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z))

end CFSG.Quasithin.Vol2.Ch11.SecE
