module

public import CFSG.Adapters.LieModelSimple
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34NotInvolvedA11
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)


theorem rest15_false_of_linear_alternating
    {G : Type} [Group G] [Finite G]
    (_hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (_hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H)
    (hXK : X ≤ K) (_hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (_hGamma : rankThreeGamma 1 3 P ≤ S.M)
    {n : ℕ} (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) : False := by
  classical
  have hKq : CFSG.Open.IsQuasisimple K := hKcomp.2.2
  have hXq : CFSG.Open.IsQuasisimple X := hXcomp.2.2
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hKq.1
  have hKr : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  have hnRank := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.le_pRank_top
    hn e Nat.prime_three (by norm_num)
  have hn11 : n ≤ 11 := by omega
  have hXs := hX.isSimpleGroup_of_mem_classicalTags (by simp [CFSG.Blueprint.classicalTags])
  have : IsSimpleGroup X := hXs
  have hZX : Subgroup.center X = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      hXs (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  let π : X →* K ⧸ Subgroup.center K :=
    (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hXK)
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : Subgroup.inclusion hXK x ∈ Subgroup.center K :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hxZX : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (congrArg (fun k : K => (k : G))
        (Subgroup.mem_center_iff.mp hxZ (Subgroup.inclusion hXK y)))
    rwa [hZX, Subgroup.mem_bot] at hxZX
  let f : X →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (e.toMonoidHom.comp π)
  have hf : Function.Injective f :=
    (alternatingGroup (Fin n)).subtype_injective.comp (e.injective.comp hπ)
  let θ : X ≃* f.range := MonoidHom.ofInjective hf
  obtain ⟨hcard, -, hnotAlt⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X
      (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.not_surjective_of_card_le_eleven
    hcard (hnotAlt (Fin 8) (by simp)) (by simpa using hn11) f.range θ.symm.toMonoidHom
    θ.symm.surjective

end CFSG.LocalAnalysis.UniquenessCase.UC22
