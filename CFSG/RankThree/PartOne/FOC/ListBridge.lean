module

public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.RankThree.PartOne.FOC

open TauCeti CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeListNative sporadicsThm3)

@[expose] def ExcListedIndex : LieTypeIndex → Prop
  | .G2 q => (q.p ≠ 2 ∧ q.exponent = 1) ∨ q.p = 2
  | .F4 q => q.p = 2 ∧ q.exponent = 1
  | .trialityD4 q => q.p = 2
  | .suzuki _ => True
  | .reeG2 m => m = 1
  | .reeF4 _ => True
  | .tits => True
  | _ => False

@[expose] def ExcListed (T : Type) [Group T] : Prop :=
  ∃ d : LieTypeIndex, ExcListedIndex d ∧ IsoLie T d

@[expose] def ClassicalFam (T : Type) [Group T] : Prop :=
  ∃ (t : StatedLieTag) (n ℓ f : ℕ), t ∈ CFSG.Blueprint.classicalTags ∧
    StatedLieAdmissible t n ℓ f ∧ CFSG.Blueprint.LieModel T t n ℓ f

section Classical

variable {T : Type} [Group T]

theorem classicalFam_of_stated {t : StatedLieTag} {n ℓ f : ℕ} (ht : t ∈ CFSG.Blueprint.classicalTags)
    (h : StatedClassicalModel T t n ℓ f) : ClassicalFam T :=
  ⟨t, n, ℓ, f, ht, h.1, Or.inl ⟨ht, h⟩⟩

theorem classicalFam_A {r : ℕ} {q : PrimePower} (hd : IsoLie T (.A r q)) : ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  have hm : CFSG.Models.LieModel T .PSL (r + 1) q.p q.exponent :=
    CFSG.RankThree.PartTwo.Sec4.Census.lieModel_of_mulEquiv e
      (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_typeA r q hv)
  have ht : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  exact ⟨.PSL, r + 1, q.p, q.exponent, ht, hm.1,
    CFSG.RankThree.PartTwo.Sec4.Census.blueprint_lieModel_of_classical ht hm⟩

theorem classicalFam_twistedA {r : ℕ} {q : PrimePower} (hd : IsoLie T (.twistedA r q)) :
    ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  exact classicalFam_of_stated (by decide)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)

theorem classicalFam_B2 {q : PrimePower} (hd : IsoLie T (.B 2 q)) : ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  exact classicalFam_of_stated (by decide)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)

theorem classicalFam_Beven {r : ℕ} {q : PrimePower} (hp : q.p = 2) (hr : 3 ≤ r)
    (hd : IsoLie T (.B r q)) : ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  exact classicalFam_of_stated (by decide)
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr e)

theorem classicalFam_D {r : ℕ} {q : PrimePower} (hd : IsoLie T (.D r q)) : ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  exact classicalFam_of_stated (by decide)
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)

theorem classicalFam_twistedD {r : ℕ} {q : PrimePower} (hd : IsoLie T (.twistedD r q)) :
    ClassicalFam T := by
  obtain ⟨hv, ⟨e⟩⟩ := hd
  exact classicalFam_of_stated (by decide)
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)

end Classical

theorem listNative_cases {T : Type} [Group T] (h : TheoremThreeListNative T) :
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
      (∃ s ∈ sporadicsThm3, Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) ∨
      ClassicalFam T ∨ ExcListed T := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · obtain ⟨q, -, -, hd⟩ := h1
    exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
  · obtain ⟨q, -, -, hd | hd⟩ := h2
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
  · exact Or.inr (Or.inr (Or.inr ⟨.reeG2 1, rfl, h3⟩))
  · obtain ⟨q, hp, hf, hd | hd | hd | hd⟩ := h4
    · exact Or.inr (Or.inr (Or.inr ⟨.G2 q, Or.inl ⟨hp, hf⟩, hd⟩))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_B2 hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
  · obtain ⟨n, h5, h12, he⟩ := h5
    exact Or.inl ⟨n, h5, h12, he⟩
  · obtain ⟨s, hs, he⟩ := h6
    exact Or.inr (Or.inl ⟨s, hs, he⟩)
  · rcases h7 with ⟨q, -, hd⟩ | ⟨m, hd⟩ | ⟨q, hq, hd | hd | hd | hd | hd | hd | hd⟩ | ⟨m, hd⟩ | hd
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inr ⟨.suzuki m, trivial, hd⟩))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_B2 hd)))
    · exact Or.inr (Or.inr (Or.inr ⟨.G2 q, Or.inr hq, hd⟩))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
    · exact Or.inr (Or.inr (Or.inr ⟨.trialityD4 q, hq, hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨.reeF4 m, trivial, hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨.tits, trivial, hd⟩))
  · obtain ⟨q, hq, hd | hd | hd⟩ := h8
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_Beven hq le_rfl hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedD hd)))
  · obtain ⟨q, hq, hf, hd | hd | hd | hd | hd | hd | hd⟩ := h9
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_A hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_twistedA hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_Beven hq (by norm_num) hd)))
    · exact Or.inr (Or.inr (Or.inl (classicalFam_D hd)))
    · exact Or.inr (Or.inr (Or.inr ⟨.F4 q, ⟨hq, hf⟩, hd⟩))

end CFSG.RankThree.PartOne.FOC
