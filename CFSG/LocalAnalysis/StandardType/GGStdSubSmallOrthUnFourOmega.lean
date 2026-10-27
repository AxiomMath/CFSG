module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourNorm
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.ComponentInitial

theorem omegaFourInput_holds : OmegaFourInput := by
  intro K _ _ _ hK X _ _ _ Q₀ hdim hQ T hTO hTel hT9 D hDΩ hDq hDn hDT
  have hdim' : finrank K X = 2 * (1 + 1) := hdim
  by_cases hplus : IsPlusType Q₀
  · have h := natCard_orthogonalGroup_of_type hQ hdim' (ε := 1) (Or.inl ⟨rfl, hplus⟩)
    rw [hK] at h
    have h72 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) = 72 := by
      have : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) : ℕ) : ℤ) = 72 := by
        rw [h]
        norm_num [Finset.Icc_self]
      exact_mod_cast this
    haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q₀) :=
      Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
    have hsolv : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q₀) :=
      isSolvable_of_card_primeFactors_le_two (by
        rw [h72, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
          Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
        decide)
    have hDle : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q₀ :=
      hDΩ.trans orthDerived_le_orthogonalGroup
    haveI : Group.IsSolvable ↥D :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hDle)
        (Subgroup.inclusion_injective hDle)
    exact not_isSolvable_of_isQuasisimple hDq this
  · have h := natCard_orthogonalGroup_of_type hQ hdim' (ε := -1) (Or.inr ⟨rfl, hplus⟩)
    rw [hK] at h
    have h120 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) = 120 := by
      have : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) : ℕ) : ℤ) = 120 := by
        rw [h]
        norm_num [Finset.Icc_self]
      exact_mod_cast this
    haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q₀) :=
      Nat.finite_of_card_ne_zero (by rw [h120]; norm_num)
    have := Subgroup.card_dvd_of_le hTO
    rw [hT9, h120] at this
    norm_num at this

end SmallOrthUn

end CFSG.StandardType

end
