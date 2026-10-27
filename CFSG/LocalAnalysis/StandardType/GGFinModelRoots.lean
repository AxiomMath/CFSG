module

public import CFSG.LocalAnalysis.StandardType.GGLangData
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Adjoint

@[expose] def langTag : StatedLieTag → Tag
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .twistedE6 => .E6
  | _ => .F4

theorem langTag_five (t : StatedLieTag) :
    langTag t = .F4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
  cases t <;> simp [langTag]

section Dictionary


theorem rank_eq_langTag {t : StatedLieTag} (f : ℕ) (ht : GGExcFive t) :
    (ggU (absTag t) 6 f).D.rank = (langTag t).rank := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mem_roots_iff_isRoot {t : StatedLieTag} (f : ℕ) (ht : GGExcFive t)
    (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    v ∈ (ggU (absTag t) 6 f).D.roots ↔
      IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) v) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact (mem_roots_F4 6 f v).trans mem_rootFinset
  · exact (mem_roots_E6 6 f v).trans mem_rootFinset
  · exact (mem_roots_E7 6 f v).trans mem_rootFinset
  · exact (mem_roots_E8 6 f v).trans mem_rootFinset
  · exact (mem_roots_E6 6 f v).trans mem_rootFinset

@[expose] noncomputable def gram : (t : StatedLieTag) → (f : ℕ) →
    Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ
  | .F4, _ => Tag.symmetrizedCartan .F4
  | .E6, _ => Tag.symmetrizedCartan .E6
  | .E7, _ => Tag.symmetrizedCartan .E7
  | .E8, _ => Tag.symmetrizedCartan .E8
  | .twistedE6, _ => Tag.symmetrizedCartan .E6
  | _, _ => 0

private def rootGramCheck (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun i => (List.finRange τ.rank).all fun j =>
    decide (τ.symmetrizedCartan i j = τ.symmetrizedCartan j i) &&
      decide (2 * τ.symmetrizedCartan i j = τ.cartan i j * τ.symmetrizedCartan i i) &&
      decide (0 < τ.symmetrizedCartan i i)

private theorem rootGramCheck_spec (τ : Tag) (h : rootGramCheck τ = true) :
    (∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.symmetrizedCartan j i) ∧
    (∀ i j : Fin τ.rank,
      2 * τ.symmetrizedCartan i j = τ.cartan i j * τ.symmetrizedCartan i i) ∧
    ∀ i : Fin τ.rank, 0 < τ.symmetrizedCartan i i := by
  simp only [rootGramCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at h
  refine ⟨fun i j => (h i j).1.1, fun i j => (h i j).1.2, fun i => ?_⟩
  exact (h i i).2

theorem isRootGram_gram {t : StatedLieTag} (f : ℕ) (ht : GGExcFive t) :
    IsRootGram (ggU (absTag t) 6 f).D (gram t f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact rootGramCheck_spec .F4 (by decide +kernel)
  · exact rootGramCheck_spec .E6 (by decide +kernel)
  · exact rootGramCheck_spec .E7 (by decide +kernel)
  · exact rootGramCheck_spec .E8 (by decide +kernel)
  · exact rootGramCheck_spec .E6 (by decide +kernel)

theorem gram_eq {t : StatedLieTag} (f : ℕ) (ht : GGExcFive t) :
    ∃ k : ℤ, 0 < k ∧ ∀ α β : Fin (ggU (absTag t) 6 f).D.rank → ℤ,
      latGram (gram t f) α β =
        k * iform (ggLangReidx (rank_eq_langTag f ht) α)
          (ggLangReidx (rank_eq_langTag f ht) β) := by
  refine ⟨1, one_pos, fun α β => ?_⟩
  rw [one_mul]
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

end Dictionary

end CFSG.StandardType.GGFinModel
