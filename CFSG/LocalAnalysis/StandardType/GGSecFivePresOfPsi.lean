module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsiGeneric

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggSecFivePres_of_psi {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n)
    (hD2 : 2 ≤ (ggU t n f).D.rank) (hU1 : GGHasWeylLift (ggU t n f).D)
    (hU2 : GGRootsGenerate (ggU t n f).D) (hU3 : GGSimpleRootGroupsRigid (ggU t n f).D)
    (hU4 : GGRootNotCentral (ggU t n f).D) (ψ : (ggU t n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFivePres p B x L D J t n f := by
  obtain ⟨ν, hν⟩ := hU1
  refine ⟨⟨hadm, hrank, hD2⟩, ν, Unit, ggRootsFamily (ggU t n f).D,
    ggRootsHom (ggU t n f).D ψ, ψ.comp ν, hν, fun _ => subset_rfl,
    injective_comp_of_rigid hν hU3 hker, ggActsLikeHom_roots hν ψ,
    ggWeylInRHom_roots hU2 ψ, ggOrbit_roots, exists_ne_one_ggRootsHom hU2 hU4 hker,
    ?_, ?_, ?_, ?_⟩
  · intro k
    rw [show (ggRootsHom (ggU t n f).D ψ k).range = ψ.range from range_ggRootsHom hU2 ψ,
      hrange]
  · have hsub : (ψ.comp ν).range ≤ ψ.range := by
      rintro x ⟨w, rfl⟩
      exact ⟨ν w, rfl⟩
    exact hsub.trans (le_of_eq hrange)
  · refine (le_ggG0_left p B x L D J).trans ?_
    rw [← hrange, ← range_ggRootsHom hU2 ψ]
    exact range_le_ggClosure ()
  · intro y K h
    refine (le_ggG0_of_ggNbr (L := L) h).trans ?_
    rw [← hrange, ← range_ggRootsHom hU2 ψ]
    exact range_le_ggClosure ()

end Main

end CFSG.StandardType

end
