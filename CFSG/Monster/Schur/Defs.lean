module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Monster.Schur

@[expose] def NoPerfectDoubleCover (G : Type*) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Group.IsPerfect E →
    Nat.card π.ker ≠ 2

theorem NoPerfectDoubleCover.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : NoPerfectDoubleCover G) : NoPerfectDoubleCover H := by
  intro E _ π hπ hE
  have hker : (e.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [← hker]
  exact hG E (e.symm.toMonoidHom.comp π) (e.symm.surjective.comp hπ) hE

end CFSG.Monster.Schur
