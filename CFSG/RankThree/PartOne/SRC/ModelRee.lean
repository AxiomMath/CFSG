module

public import CFSG.RankThree.PartOne.SRC.CentralizerKer
public import CFSG.RankThree.PartTwo.Census.Exceptional.ReeIndex

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartTwo.Census.Exceptional CFSG.Assembly.RankThreeEven
open CFSG.RankThree.CentralCover
open scoped MatrixGroups


theorem rankFourCover_ree {m : ℕ} (d : ReeG2LieIndex) (hd : d.1.fieldExponent = 2 * m + 1)
    (hm : 2 ≤ m) [Finite (FixedPointCandidate d.steinberg)] :
    RankFourCover 3 (FixedPointCandidate d.steinberg) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card d.1.fixedField = 3 ^ (2 * m + 1) := by
    rw [ValidLieTypeIndex.card_fixedField, ReeG2LieIndex.fieldOrder_eq_three_pow, hd]
  have hF4 : 4 ≤ Nat.card d.1.fixedField := by
    rw [hF]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC : commutator (SL(2, d.1.fixedField)) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF4).commutator_eq_top
  have hFfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hchar : CharP d.1.fixedField 3 := by
    have := Fintype.ofFinite d.1.fixedField
    refine charP_of_card_eq_prime_pow (f := 2 * m + 1) ?_
    rw [← Nat.card_eq_fintype_card, hF]
  have hQ : CFSG.IsQuasisimple (SL(2, d.1.fixedField)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
      d.1.fixedField le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hker : ∀ A, toQuot (reePsiH hd) hC A = 1 → A ∈ Subgroup.center (SL(2, d.1.fixedField)) := by
    intro A hA
    have hN : (toQuot (reePsiH hd) hC).ker ≤ Subgroup.center (SL(2, d.1.fixedField)) := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
        (inferInstance : (toQuot (reePsiH hd) hC).ker.Normal) with htop | hle
      · exfalso
        have hinj := toQuot_reePsiH_upper_injective hd hC
        have hc1 : ((toQuot (reePsiH hd) hC).comp (sl2UpperHom d.1.fixedField))
            (Multiplicative.ofAdd (1 : d.1.fixedField)) = 1 := by
          have : sl2UpperHom d.1.fixedField (Multiplicative.ofAdd (1 : d.1.fixedField)) ∈
              (toQuot (reePsiH hd) hC).ker := htop ▸ Subgroup.mem_top _
          exact MonoidHom.mem_ker.mp this
        have h2 : ((toQuot (reePsiH hd) hC).comp (sl2UpperHom d.1.fixedField))
            (1 : Multiplicative d.1.fixedField) = 1 := map_one _
        have h3 := hinj (hc1.trans h2.symm)
        exact one_ne_zero (Multiplicative.ofAdd.injective (h3.trans ofAdd_zero.symm))
      · exact hle
    exact hN (MonoidHom.mem_ker.mpr hA)
  exact rankFourCover_of_SL2_ker hF (by norm_num) (by omega) (toQuot (reePsiH hd) hC) hker
    (orderOf_reeTbar hd) (toQuot_reePsiH_commute hd hC)

end CFSG.RankThree.PartOne.SRC
