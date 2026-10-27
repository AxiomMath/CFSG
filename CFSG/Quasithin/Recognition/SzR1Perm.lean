module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.SzR1

variable {P : Type*} [Group P] [Finite P] {S Q : Subgroup P}

omit [Finite P] in
theorem perm_ker_eq (hQn : Q.Normal) (hS2 : IsPGroup 2 S) (hSQ : Q ≤ S)
    (hmax : ∀ N : Subgroup P, N.Normal → IsPGroup 2 N → N ≤ Q) :
    (MulAction.toPermHom P (P ⧸ S)).ker = Q := by
  have hcore : S.normalCore = (MulAction.toPermHom P (P ⧸ S)).ker :=
    Subgroup.normalCore_eq_ker S
  rw [← hcore]
  apply le_antisymm
  · exact hmax _ inferInstance (hS2.to_le (Subgroup.normalCore_le S))
  · exact Subgroup.normal_le_normalCore.mpr hSQ

theorem perm_surjective (hQn : Q.Normal) (hS2 : IsPGroup 2 S) (hSQ : Q ≤ S)
    (hmax : ∀ N : Subgroup P, N.Normal → IsPGroup 2 N → N ≤ Q) (hS3 : S.index = 3)
    (hQ6 : Q.index = 6) : Function.Surjective (MulAction.toPermHom P (P ⧸ S)) := by
  have hker := perm_ker_eq hQn hS2 hSQ hmax
  have h1 : (MulAction.toPermHom P (P ⧸ S)).ker.index =
      Nat.card (MulAction.toPermHom P (P ⧸ S)).range := Subgroup.index_ker _
  rw [hker, hQ6] at h1
  have h2 : Nat.card (Equiv.Perm (P ⧸ S)) = 6 := by
    rw [Nat.card_perm]
    have : Nat.card (P ⧸ S) = 3 := hS3
    rw [this]
    rfl
  have h3 : (MulAction.toPermHom P (P ⧸ S)).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [← h1, h2])
  exact MonoidHom.range_eq_top.mp h3

end CFSG.Quasithin.SzR1
