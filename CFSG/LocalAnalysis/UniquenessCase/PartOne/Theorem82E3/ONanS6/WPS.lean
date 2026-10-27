module

public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

noncomputable abbrev perfectCoreL (c : Ctx82E3 D) (a : G) : Subgroup G :=
  inSubgroup perfectResidual (c.L ⊓ Subgroup.centralizer ({a} : Set G))

theorem perfectCoreL_le (c : Ctx82E3 D) (a : G) :
    perfectCoreL c a ≤ c.L ⊓ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.map_subtype_le _

theorem perfectCoreL_isPerfect (c : Ctx82E3 D) (a : G) :
    Group.IsPerfect ↥(perfectCoreL c a) := by
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer ({a} : Set G)
  have hperf : Group.IsPerfect ↥(perfectResidual ↥K) :=
    (perfect_residual_characterization (G := ↥K)).2.2.1
  let e : ↥(perfectResidual ↥K) ≃* ↥(perfectCoreL c a) :=
    (perfectResidual ↥K).equivMapOfInjective K.subtype K.subtype_injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem a_mem_normalizer_of_mem_thetaComponentsAt {p : ℕ} {a : G} {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt p a) : a ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨L, hL, rfl⟩ := hJ
  have hJC : L.map (Subgroup.centralizer ({a} : Set G)).subtype ≤
      Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le L
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact Subgroup.mem_centralizer_singleton_iff.mp (hJC hj)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
