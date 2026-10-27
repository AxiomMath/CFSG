module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Defs

variable {G : Type} [Group G]

@[expose] def F112Concl (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    F112List L1' L2' S ∧ F112Second L1' L2' S

@[expose] def F112ConclLegacyBare (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    F112ListBare L1' L2' S ∧ F112Second L1' L2' S

end Defs

theorem f112LegacyPrintedError_iff : F112LegacyPrintedError ↔
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → F112ConclLegacyBare L1 L2 S :=
  ⟨fun h G _ _ L1 L2 S hh => h G L1 L2 S hh.1 hh.2.1 hh.2.2,
    fun h G _ _ L1 L2 S h1 h2 h3 => h G L1 L2 S ⟨h1, h2, h3⟩⟩

theorem f112Statement_iff : F112Statement ↔
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → F112Concl L1 L2 S := Iff.rfl


variable {G : Type} [Group G]

theorem F112Hyp.symm [Finite G] {L1 L2 S : Subgroup G} (h : F112Hyp L1 L2 S) :
    F112Hyp L2 L1 S := by
  obtain ⟨⟨h1, h2, ho⟩, hq, hn⟩ := h
  refine ⟨⟨h2, h1, by rwa [sup_comm L2 L1]⟩, by rwa [sup_comm L2 L1], hn.symm⟩

theorem f112Hyp_comm [Finite G] {L1 L2 S : Subgroup G} : F112Hyp L1 L2 S ↔ F112Hyp L2 L1 S :=
  ⟨F112Hyp.symm, F112Hyp.symm⟩

theorem F112Concl.symm {L1 L2 S : Subgroup G} (h : F112Concl L1 L2 S) : F112Concl L2 L1 S := by
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h
  exact ⟨L1', L2', hsw.symm, fun hc => hZ hc.symm, hl, h2⟩

theorem f112Concl_comm {L1 L2 S : Subgroup G} : F112Concl L1 L2 S ↔ F112Concl L2 L1 S :=
  ⟨F112Concl.symm, F112Concl.symm⟩

end CFSG.Quasithin
