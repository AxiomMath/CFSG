module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.H13.U4ParPoint
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.Quasithin.H13.U4ParPointQuot
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointModel
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.NormalClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

private theorem four_le_card_fixedField_D05 (ha : 2 ≤ a) : 4 ≤ Nat.card h.fixedField := by
  rw [h.card_fixedField]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha

private theorem isQuasisimple_sl2_D05 (ha : 2 ≤ a) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  haveI := h.finite
  exact CFSG.AGLEmbedding.LeviBlock.isQuasisimple_SL_of_four_le (K := h.fixedField)
    (four_le_card_fixedField_D05 h ha) le_rfl

theorem su4_isSLn_levHom_range : IsSLn ↥(levHom h).range 2 a := by
  haveI := h.finite
  refine ⟨h.fixedField, inferInstance, inferInstance, h.card_fixedField, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective (CFSG.Quasithin.F112R.St84.levHom_injective_u4 h)).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 h.fixedField)

theorem su4_commutator_levHom_range (ha : 2 ≤ a) :
    ⁅(levHom h).range, (levHom h).range⁆ = (levHom h).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_sl2_eq_top h ha]

theorem su4_levHom_range_le_hinf_parP (ha : 2 ≤ a) : (levHom h).range ≤ Hinf (parP h) :=
  CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual
    (su4_commutator_levHom_range h ha) (levHom_le_parP h)

theorem su4_not_isPGroup_levHom_range (ha : 2 ≤ a) : ¬ IsPGroup 2 ↥(levHom h).range := by
  intro hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h
  have hq := isQuasisimple_sl2_D05 h ha
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) h.fixedField ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) := hq.2
  haveI hnt : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
    (QuotientGroup.mk'_surjective (N := Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) h.fixedField))).nontrivial
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
    Group.isPerfect_def.mpr hq.1
  let e : Matrix.SpecialLinearGroup (Fin 2) h.fixedField ≃* ↥(levHom h).range :=
    MonoidHom.ofInjective (CFSG.Quasithin.F112R.St84.levHom_injective_u4 h)
  haveI : Group.IsPerfect ↥(levHom h).range :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  haveI : Nontrivial ↥(levHom h).range := e.injective.nontrivial
  exact Group.IsPerfect.not_isNilpotent ↥(levHom h).range hp.isNilpotent

theorem su4_isQuasisimple_bar2_hinf_parP (ha : 2 ≤ a) :
    CFSG.Open.IsQuasisimple (Bar2 (Hinf (parP h))) := by
  have e : Bar2 (Hinf (parP h)) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField := by
    rw [show Hinf (parP h) = CFSG.Quasithin.perfectCore (parP h) from
      (CFSG.Quasithin.perfectCore_eq_map_perfectResidual (parP h)).symm]
    exact modO2PerfectCoreParPEquivSL2 h ha
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e (isQuasisimple_sl2_D05 h ha)

theorem su4_normal_closure_levHom_range (ha : 2 ≤ a) :
    ∀ N : Subgroup ↥(hypSU h 2 0), N ≤ Hinf (parP h) →
      Hinf (parP h) ≤ Subgroup.normalizer (N : Set ↥(hypSU h 2 0)) →
        (levHom h).range ≤ N → N = Hinf (parP h) := by
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h
  intro N hNK hnorm hX
  exact normal_closure_top_of_perfect (Hinf (parP h))
    (CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual (parP h))
    (su4_isQuasisimple_bar2_hinf_parP h ha)
    (levHom h).range (su4_levHom_range_le_hinf_parP h ha)
    (su4_commutator_levHom_range h ha)
    (su4_not_isPGroup_levHom_range h ha) N hNK hnorm hX

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
