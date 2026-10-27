module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

private theorem quasisimple_centerQuotient_nonabelian {G : Type*} [Group G]
    (hq : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
  letI : Group.IsPerfect G := ⟨hq.1⟩
  letI : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have h := Group.IsPerfect.not_isMulCommutative (G ⧸ Subgroup.center G)
  simpa only [isMulCommutative_iff, not_forall] using h

private theorem isCatalogGroup_centerQuotient {Y : Type*} [Group Y]
    (hY : CFSG.Open.IsKGroup Y) (hq : CFSG.Open.IsQuasisimple Y) :
    CFSG.Open.IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    quasisimple_centerQuotient_nonabelian hq
  let e : (↥(⊤ : Subgroup Y) ⧸ (Subgroup.center Y).subgroupOf ⊤) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)
  have hcat := hY ⊤ (Subgroup.center Y) le_top (e.isSimpleGroup_congr.2 hsimple)
    (by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩)
  obtain ⟨i, ⟨f⟩⟩ := hcat
  exact ⟨i, ⟨e.symm.trans f⟩⟩

private theorem mem_inner_of_centerQuotientHom_mem {X : Type*} [Group X] [Group.IsPerfect X]
    {a : MulAut X} (h : centerQuotientHom X a ∈ inner (X ⧸ Subgroup.center X)) :
    a ∈ inner X := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) s
  refine ⟨x, ?_⟩
  apply centerQuotientHom_injective X
  rw [centerQuotient_conj, hs]

theorem perfectAutInner_of_schreier (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    PerfectAutInner := by
  intro X _ _ hXK hXq _ _ Y hY y hy
  haveI : Group.IsPerfect X := ⟨hXq.1⟩
  have hSsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hXq.2
  have hSnonab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a :=
    quasisimple_centerQuotient_nonabelian hXq
  have hScat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X) :=
    isCatalogGroup_centerQuotient hXK hXq
  haveI : Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) :=
    hSch (X ⧸ Subgroup.center X) hSsimple hSnonab hScat
  haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  obtain ⟨s, hs⟩ := perfect_action_inner ((centerQuotientHom X).comp Y.subtype) ⟨y, hy⟩
  have hs' : centerQuotientHom X y = MulAut.conj s := by simpa using hs
  exact mem_inner_of_centerQuotientHom_mem (a := y) ⟨s, hs'.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
