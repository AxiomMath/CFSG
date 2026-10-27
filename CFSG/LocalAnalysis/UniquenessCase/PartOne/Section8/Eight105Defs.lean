module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

variable {G : Type} [Group G] [Finite G]

@[expose] def ncl (N X : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | ∃ g ∈ N, ∃ x ∈ X, y = g * x * g⁻¹}

@[expose] def CentMod (X Q : Subgroup G) (r : G) : Prop :=
  ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ Q

structure Std8105 (D : Data G) (L P B : Subgroup G) (p n : ℕ) : Prop where
  hyp : F08.Hyp8102 D L P p n
  notB : F08.NotationB8103 L P n B
  sigma : SigmaStd D
  r61 : UC6.R6_1 D
  isU45 : IsU45 (Bar2 L) n
  even : Even n
  two_le : 2 ≤ n
  prime : p.Prime
  dvd : p ∣ 2 ^ n + 1
  evenRank : evenRank G = 3
  strong : IsStronglyPEmbedded p D.M
  sylow3 : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤
  normal : D.M ≤ normalizer (L : Set G)

structure Lines8105 (L P B B' D₀ : Subgroup G) (p n : ℕ) : Prop where
  abelian : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  notB' : F08.NotationB8103 L P n B'
  ne : B' ≠ B
  le : B' ≤ F08.KOf8103 L B
  lines : ∀ Y : Subgroup G, F08.NotationB8103 L P n Y → Y = B ∨ Y = B'
  le_D₀ : D₀ ≤ F08.KOf8103 L B
  card_D₀ : Nat.card D₀ = p
  cent_D₀ : D₀ ≤ centralizer (P : Set G)
  genRank : 2 ≤ Open.pRank p (F08.KOf8103 L B ⊔ F08.KOf8103 L B')

structure Cex8105 (D : Data G) (L P B H N : Subgroup G) : Prop where
  memH : H ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B)
  ih : ∀ H' ∈ PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B), H < H' →
    UniqueMax D.M H'
  memN : N ∈ calMOf H
  neN : N ≠ D.M
  maxN : ∀ N' ∈ calMOf H, N' ≠ D.M →
    (Nat.card (D.M ⊓ N' : Subgroup G)).factorization 2 ≤
      (Nat.card (D.M ⊓ N : Subgroup G)).factorization 2

structure Ctx8105 (D : Data G) (L P B B' D₀ H N : Subgroup G) (p n : ℕ) : Prop
    extends Std8105 D L P B p n, Lines8105 L P B B' D₀ p n, Cex8105 D L P B H N

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
