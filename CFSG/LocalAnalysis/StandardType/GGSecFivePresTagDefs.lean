module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsi
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsiSteinberg

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Facts

variable {U : Type*} [Group U]

@[expose] def GGUniversalFacts (D : UniversalRootDatum U) : Prop :=
  GGHasWeylLift D ∧ GGRootsGenerate D ∧ GGSimpleRootGroupsRigid D ∧ GGRootNotCentral D

theorem ggUniversalFacts_of_lift {D : UniversalRootDatum U} {n : Fin D.rank → U}
    {H : Fin D.rank → Subgroup U} (hr : 0 < D.rank)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hlift : GGHasWeylLift D) : GGUniversalFacts D := by
  refine ⟨hlift, ?_,
    ggSimpleRootGroupsRigid_of_rigid (ggRootGroupsRigid_of_steinberg hct hext), ?_⟩
  · unfold GGRootsGenerate ggSub
    exact hct.iSup_eq_top
  · refine ⟨Pi.single ⟨0, hr⟩ 1, single_mem_roots _, fun hle => ?_⟩
    apply hext.ne_bot _ (single_mem_roots ⟨0, hr⟩)
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    refine hext.eq_one_of_mem_normalizer ⟨0, hr⟩ u hu ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : u * h * u⁻¹ = h := by
      have := Subgroup.mem_center_iff.mp (hle hu) h
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]

theorem ggUniversalFacts_of_steinberg {D : UniversalRootDatum U} {n : Fin D.rank → U}
    {H : Fin D.rank → Subgroup U} (hr : 0 < D.rank)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hsq : ∀ i, n i * n i = 1) : GGUniversalFacts D :=
  ggUniversalFacts_of_lift hr hct hext (ggHasWeylLift_of_ctGroupDatum hct hsq)

end Facts

section Pres

@[expose] def GGTagFacts (t : StatedLieTag) (n f : ℕ) : Prop :=
  2 ≤ (ggU t n f).D.rank ∧ GGUniversalFacts (ggU t n f).D

variable {G : Type} [Group G] [Finite G]

theorem ggSecFivePres_of_psi_of_tagFacts {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n)
    (hfacts : GGTagFacts t n f) (ψ : (ggU t n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFivePres p B x L D J t n f :=
  ggSecFivePres_of_psi hadm hrank hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1
    hfacts.2.2.2.2 ψ hker hrange

end Pres

end CFSG.StandardType

end
