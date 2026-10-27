module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutData
public import CFSG.Quasithin.MS93.S46KC2Fin
public import CFSG.Quasithin.MS93.S46Stmt
public import CFSG.Quasithin.MS93.S46X3Lin
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.X3
open scoped commutatorElement Matrix

namespace KC2

section Grp

variable {𝔾 : Type} [Group 𝔾]

theorem commutator_mul_of_commute {a y z : 𝔾} (h : Commute ⁅y, z⁆ a) :
    ⁅a * y, z⁆ = ⁅y, z⁆ * ⁅a, z⁆ := by
  calc ⁅a * y, z⁆ = a * ⁅y, z⁆ * (z * a⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅y, z⁆ * a * (z * a⁻¹ * z⁻¹) := by rw [← h.eq]
    _ = ⁅y, z⁆ * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group

theorem mul_sq_of_commute {a y : 𝔾} (ha : a ^ 2 = 1) (h : Commute ⁅y, a⁆ a) :
    (a * y) ^ 2 = ⁅y, a⁆ * y ^ 2 := by
  calc (a * y) ^ 2 = a * ⁅y, a⁆ * (a * y * y) := by
        simp only [sq, commutatorElement_def]
        group
    _ = ⁅y, a⁆ * a * (a * y * y) := by rw [← h.eq]
    _ = ⁅y, a⁆ * (a ^ 2 * y ^ 2) := by
        simp only [sq]
        group
    _ = ⁅y, a⁆ * y ^ 2 := by rw [ha, one_mul]

end Grp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

variable [CharP F 2]

end KC2

end CFSG.Quasithin.MS93.S46
