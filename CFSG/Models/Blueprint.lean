module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Models

open Assembly.LowTwoRank

variable {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}

theorem LieModel.admissible (h : LieModel G t n p f) : StatedLieAdmissible t n p f :=
  h.1

theorem LieModel.statedClassicalModel_of_ne_zero (hn : n ≠ 0) (h : LieModel G t n p f) :
    StatedClassicalModel G t n p f :=
  h.2.resolve_right fun h0 => hn h0.1

theorem LieModel.statedClassicalModel (h : LieModel G t n p f)
    (ht : t ∈ Blueprint.classicalTags) : StatedClassicalModel G t n p f := by
  refine h.2.resolve_right ?_
  rintro ⟨-, d, hd, -⟩
  obtain ⟨i, hi⟩ := d
  revert hd
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> cases i <;> simp [NamesTag]

theorem LieModel.of_blueprint (ht : t ∈ Blueprint.classicalTags)
    (h : Blueprint.LieModel G t n p f) : LieModel G t n p f :=
  ⟨h.admissible, .inl (h.statedClassicalModel ht)⟩

theorem LieModel.of_blueprint_of_ne_zero (hn : n ≠ 0) (h : Blueprint.LieModel G t n p f) :
    LieModel G t n p f :=
  ⟨h.admissible, .inl (h.statedClassicalModel_of_ne_zero hn)⟩

theorem LieModel.toBlueprint (ht : t ∈ Blueprint.classicalTags) (h : LieModel G t n p f) :
    Blueprint.LieModel G t n p f :=
  .inl ⟨ht, h.statedClassicalModel ht⟩

theorem lieModel_iff_blueprint (ht : t ∈ Blueprint.classicalTags) :
    LieModel G t n p f ↔ Blueprint.LieModel G t n p f :=
  ⟨LieModel.toBlueprint ht, LieModel.of_blueprint ht⟩

end CFSG.Models
