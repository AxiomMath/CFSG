module

public import CFSG.RankThree.PartOne.CTP.StdCenter
public import CFSG.RankThree.PartOne.LSTD.ClsB

public section

namespace CFSG.RankThree.PartOne.LSTD

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem card_eq_su_three {X : Type} [Group X] (hcenter : Subgroup.center X = ⊥) {f : ℕ}
    (hf : Even f) (hf1 : 1 ≤ f)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f)
    {K₀ : Type} [Field K₀] (hU : UnitaryFieldData 2 f K₀) :
    Nat.card X = Nat.card ↥(unitarySU 2 f K₀ 3) := by
  obtain ⟨-, K₃, hK₃f, hK₃fin, hK₃, ⟨e⟩⟩ := hmodel
  have hU₃ : UnitaryFieldData 2 f K₃ := ⟨Nat.prime_two, hf1, by rw [hK₃, ← pow_mul, mul_comm]⟩
  have h1 : Nat.card X = Nat.card (X ⧸ Subgroup.center X) :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcenter).toEquiv.trans
      (QuotientGroup.quotientBot (G := X)).toEquiv)).symm
  have hsc : Nat.card ((StatedScalars (Fin 3) K₃).subgroupOf (StatedSU 3 (2 ^ f) K₃)) = 1 := by
    have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK₃ (n := 3)
      (by norm_num)).2.2
    rw [this]
    exact CTP.coprime_three_two_pow_add_one hf
  have h2 : Nat.card (StatedProj (StatedSU 3 (2 ^ f) K₃)) =
      Nat.card ↥(unitarySU 2 f K₃ 3) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((StatedScalars (Fin 3) K₃).subgroupOf (StatedSU 3 (2 ^ f) K₃))
    rw [hsc, mul_one] at this
    exact this.symm
  have h3 : Nat.card ↥(unitarySU 2 f K₃ 3) = Nat.card ↥(unitarySU 2 f K₀ 3) := by
    have e1 := card_unitarySU_three hU₃
    have e2 := card_unitarySU_three hU
    exact_mod_cast e1.trans e2.symm
  rw [h1, Nat.card_congr e.toEquiv, h2, h3]

end CFSG.RankThree.PartOne.LSTD
