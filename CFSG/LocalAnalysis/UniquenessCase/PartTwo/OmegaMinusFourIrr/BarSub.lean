module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem stableUnder_imgTil_O03 {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L U : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    StableUnder (barSub V₀ V hV L) (imgTil V₀ V hV U) := by
  intro φ hφ q hq
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L φ).1 hφ
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
  rw [actTil_mk, mem_imgTil]
  refine ⟨actStab V₀ V hV g x, ?_, rfl⟩
  rw [actStab_apply_val]
  simpa using (Subgroup.mem_normalizer_iff''.1 (hLU (L.inv_mem hgL)) x.val).1 hxU

theorem irrOn_of_isIrrOn_barSub {L A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hirr : IsIrrOn (barSub ⊥ A hA L) ⊤ ⊥) :
    UC22.IrrOn L A := by
  intro B hBA hLB
  have hstab : StableUnder (barSub ⊥ A hA L) (imgTil ⊥ A hA B) :=
    stableUnder_imgTil_O03 (V₀ := ⊥) (V := A) hA hLB
  rcases hirr.2.2.2 (imgTil ⊥ A hA B) hstab bot_le le_top with h | h
  · left
    refine le_antisymm (fun g hg => ?_) bot_le
    have hq : mkTil ⊥ A hA (IntMod.mk hA ⟨g, hBA hg⟩) ∈ imgTil ⊥ A hA B :=
      (mem_imgTil ⊥ A hA B _).2 ⟨IntMod.mk hA ⟨g, hBA hg⟩, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at hq
    have h1 : mkTil ⊥ A hA (IntMod.mk hA ⟨g, hBA hg⟩) = mkTil ⊥ A hA (1 : IntMod A hA) := by
      rw [map_one]
      exact hq
    have h2 := (mkTil_eq_iff ⊥ A hA _ _).1 h1
    rw [Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    change (IntMod.mk hA ⟨g, hBA hg⟩ : IntMod A hA).val = 1
    exact mul_inv_eq_one.mp h2
  · right
    exact s15_Two_eq_of_imgTil_eq_top hA hBA bot_le h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
