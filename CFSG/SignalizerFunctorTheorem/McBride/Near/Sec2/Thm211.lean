module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211AuxB

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem thm211a
    (h : NearAsolvAction p A G) (hss : IsSemisimple G) :
    scalJoin G A (cenIn G A) = mOf A G ∧ Group.IsSolvable (scalJoin G A (cenIn G A)) :=
  Thm211.scalJoin_semisimple h hss

theorem thm211b
    (h : NearAsolvAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) :
    scalJoin X A (cenIn G A) = scalJoin G A (cenIn G A) ⊓ X ∧
      Group.IsSolvable (scalJoin X A (cenIn G A)) :=
  Thm211.scalJoin_inf_eq h hXG hX

theorem thm211c_mul
    (h : NearAsolvAction p A G) {N : Subgroup Γ} (hNG : N ≤ G)
    (hN : IsNormalIn N (G ⊔ A)) :
    (N : Set Γ) * (norIn G (scalJoin N A (cenIn G A)) : Set Γ) = G :=
  (Thm211.frattini211 (Nat.card G) A G N rfl h hNG hN).1

theorem thm211c_le
    (h : NearAsolvAction p A G) {N : Subgroup Γ} (hNG : N ≤ G)
    (hN : IsNormalIn N (G ⊔ A)) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) (hXN : Group.IsSolvable (X ⊓ N : Subgroup Γ)) :
    X ≤ Subgroup.normalizer (scalJoin N A (cenIn G A) : Set Γ) :=
  (Thm211.frattini211 (Nat.card G) A G N rfl h hNG hN).2 X hXG hX hXN

theorem thm211d
    (h : NearAsolvAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) :
    norIn X (scalJoin X A (cenIn G A)) = scalJoin X A (cenIn G A) := by
  rw [Thm211.scalJoin_cenIn_eq hXG]
  exact Thm211.norIn_scalJoin_eq (Thm211.nearAsolvAction_of_le h hXG (le_sup_right.trans hX))

end CFSG.SignalizerFunctorTheorem.McBride.Near
