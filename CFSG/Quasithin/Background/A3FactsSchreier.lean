module

public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
public import CFSG.Milestones.CL_LIT_SQTK_simple_list

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def SimpleOutList : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Milestones.SQTKSimpleList S → Group.IsSolvable (Outer S)

@[expose] def SchreierList : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    CFSG.Milestones.SQTKSimpleList (X ⧸ Subgroup.center X) → OutSolvable X

@[expose] def SchreierSQTK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → CFSG.SectionRank.IsKGroupCat X →
    CFSG.Milestones.SQTKSimpleList (X ⧸ Subgroup.center X) → OutSolvable X

theorem schreierList_of_simpleOutList (h : SimpleOutList) : SchreierList := by
  intro X _ _ hq hlist
  have : Group.IsPerfect X := hq.1
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have : Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) := h _ hq.2.1 hq.2.2 hlist
  exact CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient X)

theorem SchreierList.toSQTK (h : SchreierList) : SchreierSQTK :=
  fun X _ _ hq _ hlist => h X hq hlist

theorem exists_section_of_surjective {G Q : Type} [Group G] [Group Q] {π : G →* Q}
    (hπ : Function.Surjective π) (K : Subgroup Q) {S : Type} [Group S] (φ : ↥K →* S)
    (hφ : Function.Surjective φ) :
    ∃ (N : Subgroup ↥(K.comap π)) (_ : N.Normal), Nonempty (↥(K.comap π) ⧸ N ≃* S) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(K.comap π) →* ↥K, ∀ x, (ρ x : Q) = π x :=
    ⟨(π.comp (K.comap π).subtype).codRestrict K fun x => x.2, fun _ => rfl⟩
  have hρs : Function.Surjective ρ := fun k => by
    obtain ⟨x, hx⟩ := hπ (k : Q)
    exact ⟨⟨x, show π x ∈ K by rw [hx]; exact k.2⟩, Subtype.ext ((hρ _).trans hx)⟩
  exact ⟨(φ.comp ρ).ker, inferInstance,
    ⟨QuotientGroup.quotientKerEquivOfSurjective _ (hφ.comp hρs)⟩⟩

theorem sqtkSimpleList_center_quotient_of_component
    {G : Type} [Group G] [Finite G]
    (hG : CFSG.SectionRank.IsSQTKCat G) {K : Subgroup (G ⧸ CFSG.solvableRadical G)}
    (hK : CFSG.IsComponent K) :
    CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨-, hs, hnonab⟩ := hK.1
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_section_of_surjective
    (QuotientGroup.mk'_surjective (CFSG.solvableRadical G)) K
    (QuotientGroup.mk' (Subgroup.center ↥K)) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (↥(K.comap (QuotientGroup.mk' (CFSG.solvableRadical G))) ⧸ N) :=
    e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnonab
  exact A36A.a23List_of_mulEquiv e.symm (CFSG.Milestones.cl_lit_sqtk_simple_list_section G hG _ N
    ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩)

end A3Facts

end CFSG.Quasithin
