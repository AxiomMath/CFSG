module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KFactL2CentThreePrime : Prop :=
  ∀ (m : ℕ) (H : Subgroup ↥(projSL 2 (GaloisField 2 m))), ⁅H, H⁆ = H → H ≠ ⊤ →
    ∀ x ∈ H, orderOf x = 3 →
      ∃ g ∈ Subgroup.centralizer ({x} : Set ↥(projSL 2 (GaloisField 2 m))),
        Nat.Coprime (orderOf g) 3 ∧ g ∉ H

@[expose] def KFactL34QEightTop : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 2)) →
    ∀ (Bb Q : Subgroup X), Nat.card Bb = 9 → Nat.card Q = 8 →
      Q ≤ Subgroup.normalizer (Bb : Set X) →
      ∀ (J O : Subgroup (MulAut X)), O ≤ J → (O.subgroupOf J).Normal →
        Q.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (J : Set (MulAut X)) →
        Q.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (O : Set (MulAut X)) →
        Nat.Coprime (Nat.card O) 3 → (∃ g ∈ J, J ≤ O ⊔ Subgroup.zpowers g) →
        Nat.Coprime (O.relIndex J) 6 → J = O

@[expose] def Step204FinalL2CYcThreePrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
          ∀ y ∈ yTwenty X c ⊓ Subgroup.centralizer ({c} : Set G), Nat.Coprime (orderOf y) 3 →
            y ∈ (yTwenty X c ⊓ M) ⊔ oThreePrimeYR M X T c

end CFSG.RankThree.PartTwo.Sec20
