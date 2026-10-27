module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunSet
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthTwoD
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F14

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie (commute_of_map_mem_map)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (excOth_sl2_noncomm)
open scoped MatrixGroups

theorem exists_noncommuting_map_of_equiv_sl2 {U X F : Type} [Group U] [Group X] [Field F]
    (ψ : U →* X) (hker : ψ.ker ≤ Subgroup.center U) {R : Subgroup U}
    (e : R ≃* SL(2, F)) : ∃ a ∈ R, ∃ b ∈ R, ψ a * ψ b ≠ ψ b * ψ a := by
  let ρ : SL(2, F) →* X := ψ.comp (R.subtype.comp e.symm.toMonoidHom)
  have hρker : ∀ B : SL(2, F), ρ B = 1 → (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro B hB
    have hZ : (e.symm B : U) ∈ Subgroup.center U := hker (MonoidHom.mem_ker.mpr hB)
    have hBZ : B ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro A
      apply e.symm.injective
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using Subgroup.mem_center_iff.mp hZ (e.symm A : U)
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hBZ
    rw [← hr]
    simp [Matrix.scalar_apply]
  by_contra! hcomm
  have hρcomm : ∀ A B : SL(2, F), Commute (ρ A) (ρ B) := by
    intro A B
    exact hcomm (e.symm A) (e.symm A).2 (e.symm B) (e.symm B).2
  exact excOth_sl2_noncomm ρ hρker (hρcomm _ _)

theorem map_ne_of_commuting_of_equiv_sl2 {U X F : Type} [Group U] [Group X] [Field F]
    (ψ : U →* X) (hker : ψ.ker ≤ Subgroup.center U) {R S : Subgroup U}
    (e : R ≃* SL(2, F)) (hc : ∀ a ∈ R, ∀ b ∈ S, a * b = b * a) :
    R.map ψ ≠ S.map ψ := by
  intro heq
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncommuting_map_of_equiv_sl2 ψ hker e
  have haS : ψ a ∈ S.map ψ := heq ▸ Subgroup.mem_map_of_mem ψ ha
  have hcomm := commute_of_map_mem_map ψ hker hc ha haS b hb
  exact hab (by rw [← map_mul, ← map_mul, hcomm])

end CFSG.LocalAnalysis.UniquenessCase.UC22.F14
