module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviLine


public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem omegaMinus8Natural_holds (K : Type) [Field K] [Finite K] (b c : K) (m : ℕ)
    (hK : Nat.card K = 2 ^ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OmegaMinus8Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
      (CFSG.Quasithin.H.natImage
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) m := by
  have hm : 1 ≤ m := by
    by_contra h
    rw [not_le] at h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  haveI : CharP K 2 :=
    ringChar.of_eq
      (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hm hK)
  exact O8Levi.omegaMinus8Natural_of_t3H hirr (O8Levi.omegaMinus8Line_t3H hirr hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22
