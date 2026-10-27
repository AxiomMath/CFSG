module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixSpU
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixRee
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixExc

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def K424SixSp4Odd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Odd n →
    Nonempty (X ≃* projSp 2 (GaloisField 2 n)) → IsQuasisimple X → Census424 X

theorem k424Inner46SixRest_of
    (hSp : K424SixSp4Odd) (hL : K424PairingLie) (hR : Sec8.ReeF4OrderThreeConj)
    (hT : Res417Six.K417TitsCentThree) : K424Inner46SixRest := by
  intro X _ _ hX hq hZ hSL
  rcases hX with ⟨n, hn, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ | ⟨f, hG | hD | hF | hT'⟩
  · rcases Nat.even_or_odd n with hev | hodd
    · exact Res4Seven.census424_of_sp4_even hn hev e
    · exact hSp X n hodd ⟨e⟩ hq
  · rcases Nat.even_or_odd n with hev | hodd
    · exact Res4Seven.census424_of_u4_even hn hev e
    · exact Res4Seven.census424_of_u4_odd hodd e
  · have hX46 : IsList46 X :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨f, Or.inl hG⟩)))))))
    exact Res4Seven.census424_of_g2_pairing hL hX46 hq hZ hSL hG
  · have hX46 : IsList46 X :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr
        ⟨f, Or.inr (Or.inl hD)⟩)))))))
    exact Res4Seven.census424_of_d4_pairing hL hX46 hq hZ hSL hD
  · exact Res4Seven.census424_of_twistedF4 hR hF
  · exact Res4Seven.census424_of_tits hT hT'

end CFSG.RankThree.PartTwo.Sec4
