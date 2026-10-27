module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixExc

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def K424ThreeSp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 3 < p →
    Nonempty (X ≃* projSp 2 (GaloisField p 1)) → Census424 X

@[expose] def K424ThreeL4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 3 < p →
    ((p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1)))) → Census424 X

theorem k424Inner46Three_of
    (hL : K424PairingLie) (hSp : K424ThreeSp4) (hL4 : K424ThreeL4) : K424Inner46Three := by
  intro X _ _ hX hq hZ hSL
  have hX46 : IsList46 X := Or.inr (Or.inr (Or.inl hX))
  obtain ⟨p, hp, hp3, hG | he | ⟨h1, he⟩ | ⟨h2, he⟩⟩ := hX
  · exact Res4Seven.census424_of_g2_pairing hL hX46 hq hZ hSL hG
  · exact hSp X p hp3 he
  · exact hL4 X p hp3 (Or.inl ⟨h1, he⟩)
  · exact hL4 X p hp3 (Or.inr ⟨h2, he⟩)

end CFSG.RankThree.PartTwo.Sec4
