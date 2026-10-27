module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMData
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrLabel_perfect_normalizer {S : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs K : Subgroup G} (h : GGInnerDiagOnLabel S p Bs K) :
    commutator ↥K = ⊤ ∧ Bs ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨hperf, ?_⟩
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  exact hP.2.1

private theorem qTwoNbrLabel_lieModel_of_su {H : Type} [Group H] [Finite H] {m f : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (e : H ⧸ Subgroup.center H ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) :
    LieModel (H ⧸ Subgroup.center H) .PSU m 2 f := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hf, by omega, ?_⟩, K, inferInstance, inferInstance,
    hK, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by omega)
  · exact ⟨show H ⧸ Subgroup.center H ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU m (2 ^ f) K) from e⟩

theorem qTwoNbrLabel_lieModel {Bs K : Subgroup G}
    (hmark : GGInnerDiagOnLabel ggRowP_ESU 3 Bs K)
    (hfield : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → lab.n = 1) :
    ∃ d : ℕ, 4 ≤ d ∧ LieModel (↥K ⧸ Subgroup.center ↥K) .PSU d 2 1 := by
  obtain ⟨lab, hΛ, hhas, hrest⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨_, _, _, _, _, hP⟩ := hrest
  have hrow : ggRowP_ESU 3 lab := hP.1
  have hn : lab.n = 1 := hfield lab hΛ hhas
  obtain ⟨F, hF, hFfin, d, hcard, h4d, -, hQ'⟩ := ggNSLieN3A_esuRecipe hrow hhas
  obtain ⟨e⟩ := hQ'
  letI := hF
  letI := hFfin
  refine ⟨d, h4d, ?_⟩
  rw [hn] at hcard e
  exact qTwoNbrLabel_lieModel_of_su hcard h4d le_rfl e

end CFSG.StandardType.QTwo

end
