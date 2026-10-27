module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.S146zY

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outer_comm_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ x y : Outer X, x * y = y * x) : ∀ x y : Outer Y, x * y = y * x := by
  intro x y
  obtain ⟨x, rfl⟩ := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).surjective x
  obtain ⟨y, rfl⟩ := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).surjective y
  rw [← map_mul, ← map_mul, h]

theorem outer_comm_of_forall_inner {X : Type*} [Group X]
    (h : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g) : ∀ x y : Outer X, x * y = y * x := by
  have key : ∀ x : Outer X, x = 1 := by
    intro x
    obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, hg⟩ := h φ
    exact (QuotientGroup.eq_one_iff φ).2 ⟨g, hg.symm⟩
  intro x y
  rw [key x, key y]

end CFSG.Quasithin.S146zY
