module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem eq_bot_of_isPerfect_of_le_normalizer_U3 {H : Type} [Group H] [Finite H] {m : ℕ}
    (hm : 2 ≤ m) (e : H ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 m) {D Kb : Subgroup H}
    (hD : IsPGroup 2 D) (hD1 : D ≠ ⊥) (hK : Group.IsPerfect Kb)
    (hKD : Kb ≤ Subgroup.normalizer (D : Set H)) : Kb = ⊥ := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 2 m := by
    refine ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩
    have h2 : 2 ^ m = 2 := congrArg Prod.snd h
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hL : CFSG.Blueprint.LieModel H .PSU 3 2 m :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e⟩
  exact CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
    hL hD hD1 hK hKD

end CFSG.RankThree.PartTwo.Sec20
