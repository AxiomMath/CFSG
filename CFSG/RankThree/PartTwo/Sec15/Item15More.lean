module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item154 (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0 A LB, ∀ X ∈ scriptY4 A LB, X ≤ Y →
    ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
      ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨
      (∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) ∧
        IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n ∧
        L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L) ∨
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∧
        (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).relIndex R = 4 ∧
        (∀ r ∈ R, r ^ 2 ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) ∧
        ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
          R ⊓ Subgroup.centralizer ({d} : Set G) ≤ centralizerSection Y (CFSG.Open.pCoreOf 2 Y))

@[expose] def gam155 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y X : Subgroup G) :
    Set (Subgroup G) :=
  {K | K ∈ scriptY0Star A LB ∧ X ≤ K ∧ Y ≤ Subgroup.normalizer (K : Set G)}

@[expose] def omg155 (A X : Subgroup G) : Prop :=
  ((¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) ∧
      IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) ∨
    ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L'

@[expose] noncomputable def Item155 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY3 A LB, oPrimeResidualOf 3 Y ∈ scriptY4 A LB →
    Y = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 Y →
      (omg155 A (oPrimeResidualOf 3 Y) → (gam155 A LB Y (oPrimeResidualOf 3 Y)).Nonempty) ∧
      ∀ K ∈ gam155 A LB Y (oPrimeResidualOf 3 Y),
        (omg155 A (oPrimeResidualOf 3 Y) ∨
          K = oPrimeResidualOf 3 Y ⊔ CFSG.Open.pCoreOf 2 K) →
        ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
          delta A LB M ≤ Subgroup.normalizer (K : Set G)

end CFSG.RankThree.PartTwo.Sec15
