module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryTrans
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherProjectiveAction

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {m : ℕ} {F' : Type} [Field F']

theorem model3_unitary_generation (hm : 2 ≤ m) (hF' : UnitaryFieldData 2 m F')
    (R : Sylow 2 ↥(unitarySU 2 m F' 3)) {L : Submodule F' (Fin 3 → F')}
    (hL : L ∈ isotropicLines hF' 3)
    (hZ : (center ↥(R : Subgroup ↥(unitarySU 2 m F' 3))).map
        (R : Subgroup ↥(unitarySU 2 m F' 3)).subtype = isotropicTransvectionGroup hF' 3 L)
    (hfix : ∀ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L)
    (τ : ↥(unitarySU 2 m F' 3)) (hτ : τ⁻¹ • L ≠ L) :
    (R : Subgroup ↥(unitarySU 2 m F' 3)) ⊔
      (R : Subgroup ↥(unitarySU 2 m F' 3)).map (MulAut.conj τ⁻¹).toMonoidHom = ⊤ := by
  have hq4 : 4 ≤ 2 ^ m := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
    simpa using h
  have hnq : ((3 : ℕ), 2 ^ m) ≠ ((3 : ℕ), 2) := by
    intro h
    have h2 : 2 ^ m = 2 := congrArg Prod.snd h
    omega
  have hTL : isotropicTransvectionGroup hF' 3 L ≤ (R : Subgroup ↥(unitarySU 2 m F' 3)) := by
    rw [← hZ]
    exact Subgroup.map_subtype_le _
  have hL' : τ⁻¹ • L ∈ isotropicLines hF' 3 :=
    (UnitaryHigher.unitary_point_conjugation hF' τ⁻¹ hL).1
  have hTL' : isotropicTransvectionGroup hF' 3 (τ⁻¹ • L) ≤
      (R : Subgroup ↥(unitarySU 2 m F' 3)) ⊔
        (R : Subgroup ↥(unitarySU 2 m F' 3)).map (MulAut.conj τ⁻¹).toMonoidHom := by
    rw [← (UnitaryHigher.unitary_point_conjugation hF' τ⁻¹ hL).2.1]
    exact le_sup_of_le_right (Subgroup.map_mono hTL)
  have hall : ∀ M : Submodule F' (Fin 3 → F'), M ∈ isotropicLines hF' 3 →
      isotropicTransvectionGroup hF' 3 M ≤
        (R : Subgroup ↥(unitarySU 2 m F' 3)) ⊔
          (R : Subgroup ↥(unitarySU 2 m F' 3)).map (MulAut.conj τ⁻¹).toMonoidHom := by
    intro M hM
    by_cases hML : M = L
    · rw [hML]
      exact hTL.trans le_sup_left
    · obtain ⟨v, hv, hvM⟩ := model3_unitary_transitive hF' R hL hfix hL' hM hτ hML
      subst hvM
      rw [← (UnitaryHigher.unitary_point_conjugation hF' v hL').2.1]
      have hvS : v ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)) ⊔
          (R : Subgroup ↥(unitarySU 2 m F' 3)).map (MulAut.conj τ⁻¹).toMonoidHom :=
        Subgroup.mem_sup_left hv
      rintro _ ⟨y, hy, rfl⟩
      show v * y * v⁻¹ ∈ _
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hvS (hTL' hy)) (Subgroup.inv_mem _ hvS)
  have hgen := UnitaryHigher.unitary_point_normal_generation hF' (le_refl 3) hnq hL
  rw [eq_top_iff, ← hgen]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨g, hxg⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hgL, hmap, -, -⟩ := UnitaryHigher.unitary_point_conjugation hF' g hL
  have hxg' : x ∈ isotropicTransvectionGroup hF' 3 (g • L) := by
    rw [← hmap]
    exact hxg
  exact hall (g • L) hgL hxg'

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
