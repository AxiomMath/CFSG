module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def centFitting (M : Subgroup G) : Subgroup G :=
  barPreimage M (Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 M) : Set (Bar2 M)))

@[expose] def IsInnerCartanOnL (A K L T : Subgroup G) (m : ℕ) : Prop :=
  A ≤ K ⊓ Subgroup.normalizer (T : Set G) ∧ IsCyclic ↥A ∧ Nat.card A = 2 ^ m - 1 ∧
    A ≤ Subgroup.normalizer (L : Set G) ∧
    (∀ a ∈ A, ∃ ℓ : Bar2 L, InducedBar L a (MulAut.conj ℓ)) ∧
    (∀ a ∈ A, InducedBar L a 1 → a = 1)

@[expose] def S23_29 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ K ∈ calC D.M,
    (∃ m : ℕ, 1 ≤ m ∧ m ∣ CFSG.Open.pRank 2 D.Z ∧
        (IsSz (Bar2 K) m ∨ ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m)) ∧
        ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 K) q ∧
        ⁅CFSG.Quasithin.opResidual 3 c.B, K⁆ ≤ CFSG.Open.pCoreOf 2 K)

end CFSG.LocalAnalysis.UniquenessCase.UC22
