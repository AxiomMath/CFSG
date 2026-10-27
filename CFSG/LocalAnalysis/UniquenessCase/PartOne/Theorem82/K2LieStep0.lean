module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2Reduction
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ONAut
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup

private lemma k2Lie_of_k2Simple_conj (K : Type) [Group K] (y : K) :
    CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter K (MulAut.conj y) =
      MulAut.conj (QuotientGroup.mk y) := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H z => rfl

private lemma k2Lie_of_k2Simple_map_innAut (K : Type) [Group K] :
    (innAut K).map (CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter K) =
      innAut (K ⧸ Subgroup.center K) := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨y, rfl⟩ := hψ
    exact ⟨QuotientGroup.mk y, (k2Lie_of_k2Simple_conj K y).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
    exact ⟨MulAut.conj y, ⟨y, rfl⟩,
      by simpa [QuotientGroup.mk'_apply] using k2Lie_of_k2Simple_conj K y⟩

private lemma k2Lie_of_k2Simple_comap_innAut (K : Type) [Group K] (hK : commutator K = ⊤) :
    (innAut (K ⧸ Subgroup.center K)).comap
        (CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter K) = innAut K := by
  have hinj := CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter_injective hK
  apply le_antisymm
  · rintro φ ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) x
    refine ⟨y, hinj ?_⟩
    rw [k2Lie_of_k2Simple_conj K y]
    simpa [QuotientGroup.mk'_apply] using hx
  · rintro φ ⟨y, rfl⟩
    exact ⟨QuotientGroup.mk y, (k2Lie_of_k2Simple_conj K y).symm⟩

theorem k2Lie_of_k2Simple (h : K2Simple) : K2Lie := by
  intro Y _ _ fam r f hY _ R hR hS hnot
  obtain ⟨hq, _, hfam⟩ := hY
  haveI : Group.IsPerfect Y := hq.1
  have hperf : commutator Y = ⊤ := Group.isPerfect_def.mp hq.1
  have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot Y
  let ρ : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) :=
    CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter Y
  have hρinj : Function.Injective ρ :=
    CFSG.HardMathSupport.Solomon.Coordinator.mulAutQuotCenter_injective hperf
  let R' : Subgroup (MulAut (Y ⧸ Subgroup.center Y)) := R.map ρ
  have hR' : IsPGroup 3 R' := hR.map ρ
  have hinn : (innAut Y).map ρ = innAut (Y ⧸ Subgroup.center Y) :=
    k2Lie_of_k2Simple_map_innAut Y
  have hinf : R' ⊓ innAut (Y ⧸ Subgroup.center Y) = (R ⊓ innAut Y).map ρ := by
    show R.map ρ ⊓ innAut (Y ⧸ Subgroup.center Y) = (R ⊓ innAut Y).map ρ
    rw [Subgroup.map_inf_eq R (innAut Y) ρ hρinj, hinn]
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 (R' ⊓ innAut (Y ⧸ Subgroup.center Y))
      (innAut (Y ⧸ Subgroup.center Y)) := by
    rw [hinf, ← hinn]
    exact CFSG.ComponentClassification.AschbacherTheorem3.IsSylowOf.map hS ρ
  have hnot' : ¬ R' ≤ innAut (Y ⧸ Subgroup.center Y) := by
    intro hle
    apply hnot
    rw [← k2Lie_of_k2Simple_comap_innAut Y hperf]
    intro φ hφ
    exact hle (Subgroup.mem_map_of_mem ρ hφ)
  have hrank : pRank 3 R' = pRank 3 R :=
    (CFSG.pRank_congr_of_mulEquiv (Subgroup.equivMapOfInjective R ρ hρinj) 3).symm
  rw [← hrank]
  exact h (Y ⧸ Subgroup.center Y) fam r f hfam hZ R' hR' hS' hnot'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
