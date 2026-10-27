module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualSL3
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualM22
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo.Sec4.ResidualGen
open CFSG.Assembly.RankThreeEven (projSL)

theorem residualAt_of_data {T : Type} [Group T] [Finite T]
    (hT : ResidualData T) : ResidualAt T := by
  intro X _ _ hX hXp hO2 K _ hK h9 hψ
  obtain ⟨ψ⟩ := hψ
  exact isQuasisimple_of_residualData hT hX hXp hO2 K hK h9 ψ

theorem residualAt_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ResidualAt T) : ResidualAt T' := by
  intro X _ _ hX hXp hO2 K _ hK h9 hψ
  obtain ⟨ψ⟩ := hψ
  exact h X hX hXp hO2 K hK h9 ⟨ψ.trans e.symm⟩

theorem residualSL3_of_one_le :
    ∀ m : ℕ, 1 ≤ m → ResidualAt (projSL 3 (GaloisField 2 (2 * m))) := by
  intro m hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 (2 * m)) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 3 ∣ Nat.card (GaloisField 2 (2 * m)) - 1 := by
    rw [hcard, pow_mul]
    have : (2 ^ 2) ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  exact residualAt_of_mulEquiv (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 _).symm
    (residualAt_of_data (residualData_projectiveSL h4 h3))

theorem residualSL3 :
    ∀ m : ℕ, 2 ≤ m → ResidualAt (projSL 3 (GaloisField 2 (2 * m))) :=
  fun m hm => residualSL3_of_one_le m (by omega)

theorem residualM22 :
    ResidualAt Blueprint.NativeSporadic.M22 :=
  residualAt_of_data residualData_M22

end CFSG.RankThree.PartTwo.Sec4
