module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FLinear
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryMain
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoFinal
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Assembly.RankThreeEven (projSL projSU)

section Linear


theorem seitz27_l3pi_of_planes (hA : Sec19.SeitzThreeLThreePi) {n : ℕ} (hn : 12 ≤ n)
    (h3n : 3 ∣ n) (hev : Even n) : Seitz27 (projSL 3 (GaloisField 2 n)) := by
  obtain ⟨m, rfl⟩ := h3n
  have hm : 4 ≤ m := by omega
  have hmev : Even m := by
    rcases hev with ⟨a, ha⟩
    exact ⟨a - m, by omega⟩
  have hmod : 2 ^ m % 3 = 1 := by
    obtain ⟨a, rfl⟩ := hmev
    rw [← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  have h3 : (3 : GaloisField 2 (3 * m)) ≠ 0 := by
    have : (3 : GaloisField 2 (3 * m)) = 1 := by
      have h2 : (2 : GaloisField 2 (3 * m)) = 0 := CharP.cast_eq_zero (GaloisField 2 (3 * m)) 2
      calc (3 : GaloisField 2 (3 * m)) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [this]
    exact one_ne_zero
  have hF : Nat.card (GaloisField 2 (3 * m)) = 2 ^ (3 * m) :=
    GaloisField.card 2 (3 * m) (by omega)
  exact seitz27_of_mulEquiv (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 _)
    (seitz27_projectiveSL_cubic hA h3 hm hmod hF)

end Linear

section Unitary


theorem seitz27_u3pi_of_planes (hA : Sec19.SeitzThreeLThreePi) {n : ℕ} (hn : 9 ≤ n)
    (h3n : 3 ∣ n) (hodd : Odd n) : Seitz27 (projSU 3 2 n) := by
  obtain ⟨m, rfl⟩ := h3n
  have hm : 3 ≤ m := by omega
  have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
  have hmod : 2 ^ m % 3 = 2 := by
    obtain ⟨a, rfl⟩ := hmodd
    rw [pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * m)
      (GaloisField 2 (2 * (3 * m))) :=
    Sec4.unitaryFieldData_galoisField 2 (3 * m) (by omega)
  exact seitz27_of_mulEquiv (Sec4.projSUEquivUnitaryPSU 2 (3 * m) hU)
    (seitz27_unitaryPSU_cubic hA hm hmod hU)

end Unitary

section Rows


theorem seitz27_l3pi {n : ℕ} (hn : 12 ≤ n) (h3n : 3 ∣ n) (hev : Even n) :
    Seitz27 (projSL 3 (GaloisField 2 n)) :=
  seitz27_l3pi_of_planes
    (Sec19.SeitzScopeProof.seitzThreeLThreePi_of_field Sec19.seitzThreeLThreePiField_holds)
    hn h3n hev

theorem seitz27_u3pi {n : ℕ} (hn : 9 ≤ n) (h3n : 3 ∣ n) (hodd : Odd n) :
    Seitz27 (projSU 3 2 n) :=
  seitz27_u3pi_of_planes
    (Sec19.SeitzScopeProof.seitzThreeLThreePi_of_field Sec19.seitzThreeLThreePiField_holds)
    hn h3n hodd

end Rows

end CFSG.RankThree.PartTwo.Sec4.E27
