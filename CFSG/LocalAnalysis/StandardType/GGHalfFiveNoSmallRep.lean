module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import CFSG.LieType.SeitzGeneration.HyperIrrBlock

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem sl3_hom_trivial_of_finrank_le_two {V : Type} [AddCommGroup V] [Module F4 V]
    [Module.Finite F4 V] (hV : Module.finrank F4 V ≤ 2)
    (ρ : SpecialLinearGroup (Fin 3) F4 →* Module.End F4 V)
    (s : SpecialLinearGroup (Fin 3) F4) : ρ s = 1 := by
  let d := Module.finrank F4 V
  have hd : d ≤ 2 := hV
  let b : Module.Basis (Fin d) F4 V := Module.finBasis F4 V
  let e : (Module.End F4 V)ˣ ≃* GL (Fin d) F4 :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let ρ' : SpecialLinearGroup (Fin 3) F4 →* (Module.End F4 V)ˣ := ρ.toHomUnits
  haveI : Fintype F4 := Fintype.ofFinite F4
  have hcard4 : Fintype.card F4 = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hd0 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hGL : Nat.card (GL (Fin d) F4) ≤ 180 := by
    rcases hd0 with h | h | h <;> rw [h, Matrix.card_GL_field, hcard4] <;> norm_num
  have hrange : Nat.card (ρ'.range) ≤ 180 := by
    have hcardmap : Nat.card (ρ'.range.map e.toMonoidHom) = Nat.card (ρ'.range) :=
      Subgroup.card_map_of_injective (K := ρ'.range) (f := e.toMonoidHom) e.injective
    have hle : Nat.card (ρ'.range.map e.toMonoidHom) ≤ Nat.card (GL (Fin d) F4) :=
      Subgroup.card_le_card_group (ρ'.range.map e.toMonoidHom)
    rw [hcardmap] at hle
    exact le_trans hle hGL
  have hQ : Nat.card (SpecialLinearGroup (Fin 3) F4) = 60480 := by
    rw [Matrix.card_SL_field, hcard4]
    norm_num [Fin.prod_univ_three]
  have hprod : Nat.card (ρ'.ker) * Nat.card (ρ'.range) = 60480 := by
    have hquot : Nat.card (SpecialLinearGroup (Fin 3) F4 ⧸ ρ'.ker) = Nat.card (ρ'.range) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv
    rw [← hquot, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
    exact hQ
  have hcenter : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F4)) ≤ 3 := by
    have h1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F4)) =
        Nat.card (rootsOfUnity (Fintype.card (Fin 3)) F4) :=
      Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F4) (0 : Fin 3)).toEquiv
    rw [h1]
    have h3 : Fintype.card (Fin 3) = 3 := rfl
    rw [h3]
    exact card_rootsOfUnity F4 3
  have hN : 336 ≤ Nat.card (ρ'.ker) := by
    by_contra h
    have hle : Nat.card (ρ'.ker) ≤ 335 := by omega
    have hmul := Nat.mul_le_mul hle hrange
    rw [hprod] at hmul
    omega
  have hnotle : ¬ ρ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F4) := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    omega
  obtain ⟨a, haN, hac⟩ := Set.not_subset.1 hnotle
  have htop : ρ'.ker = ⊤ :=
    CFSG.LieType.SeitzGeneration.eq_top_of_normal_of_not_mem_center
      (F := F4) (p := 3) (by norm_num) (N := ρ'.ker) haN hac
  have h1 : ρ' s = 1 := MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top s)
  calc ρ s = (ρ' s : Module.End F4 V) := (MonoidHom.coe_toHomUnits ρ s).symm
    _ = 1 := by simp [h1]

end CFSG.StandardType.GGHalf

end