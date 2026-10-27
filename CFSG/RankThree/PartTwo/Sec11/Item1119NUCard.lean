module

import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.GorensteinWalter

namespace Item1119NU

theorem three_pow_dvd_card_psl2 {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 3 ^ m ∣ Nat.card F ^ 2 - 1) : 3 ^ m ∣ Nat.card (PSL2 F) := by
  have h1 := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  have hle := CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.card_center_sl2_le_two F
  have hpos : 0 < Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Nat.card_pos
  have hcop : Nat.Coprime (3 ^ m)
      (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    apply Nat.Coprime.pow_left
    interval_cases h : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    · exact Nat.coprime_one_right 3
    · decide
  have hdvd : 3 ^ m ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [h1]
    exact Dvd.dvd.mul_left hm _
  exact hcop.dvd_of_dvd_mul_right hdvd

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
