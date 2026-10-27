module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx215 (D : Data G) (Ch : Choice2011 G) extends Ctx21 D Ch where
  L : Subgroup G
  hL : L ∈ calC D.M
  a : G
  haB : a ∈ B
  ha_prime : (orderOf a).Prime
  ha_ne_two : orderOf a ≠ 2
  ha_not_mem : a ∉ Subgroup.normalizer (L : Set G)

@[expose] def R72Shape (p : ℕ) (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, LieModel X .PSL 2 p n) ∨ (∃ n : ℕ, LieModel X .PSU 3 p n) ∨
    (p = 3 ∧ (F07.IsReeType X 1 ∨ IsSpor X .M11 ∨ IsL3 X 2)) ∨
    (p = 5 ∧ (F07.IsAutSz X 5 ∨ LieModel X .Tits 0 2 1 ∨ IsSpor X .McL ∨ IsAlt X 10)) ∨
    (p = 11 ∧ IsSpor X .J4)

theorem r72Shape_of_r72 {D : Data G} (h72 : F07.R72 D) {p : ℕ} {H : Subgroup G}
    (hH : F07.Sec7Hyp D p H) :
    genFittingFStar (F07.QuotK7 p H) ≤ F07.ImageModK p H (Opp p H) ∧
      R72Shape p (F07.LKQuot7 p H) :=
  h72 p H hH

@[expose] def KStrongEmbedded72 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    CFSG.pPrimeCore p X = ⊥ → ∀ L : Subgroup X, L.Normal → genFittingFStar X ≤ L →
      R72Shape p ↥L → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        IsSolvable ↥N ∨
          (p = 5 ∧ IsAlt ↥L 10 ∧
            ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S],
              IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5)

@[expose] def KThinSimple : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsKGroup Q → IsSimpleGroup Q →
    (∃ x y : Q, x * y ≠ y * x) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Sylow p Q, IsCyclic ↥(P : Subgroup Q)) →
        (∃ n : ℕ, IsL2 Q n) ∨ (∃ n : ℕ, IsSz Q n) ∨
          (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd Q q) ∨ IsJ1 Q

@[expose] def KOddOutInner : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    ((∃ k : ℕ, 1 ≤ k ∧ IsL2 Q (2 ^ k)) ∨
        (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd Q q) ∨ IsJ1 Q) →
      ∀ θ : MulAut Q, Odd (orderOf θ) →
        θ ∈ (MulAut.conj : Q →* MulAut Q).range
