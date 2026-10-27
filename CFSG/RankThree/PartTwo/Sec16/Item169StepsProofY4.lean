module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Proof1610

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_eq_bot_of_coprime {X : Subgroup G} (hX : ¬ 3 ∣ Nat.card X) :
    oPrimeResidualOf 3 X = ⊥ := by
  have hres : oPrimeResidual 3 ↥X = ⊥ := by
    rw [oPrimeResidual, Subgroup.closure_eq_bot_iff]
    rintro x ⟨k, hk⟩
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
    have hcop : Nat.Coprime (3 ^ k) (Nat.card X) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX)
    have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp this
  rw [oPrimeResidualOf, hres, Subgroup.map_bot]

end Proof1610

open Proof1610

end CFSG.RankThree.PartTwo.Sec16
