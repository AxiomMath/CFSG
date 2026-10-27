module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma214AuxLocal

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem lemma214
    {X W : Subgroup Γ} (h : NearAction p A X) (hss : IsSemisimple X) {a : Γ}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hsolv : Group.IsSolvable (cenIn X {a} : Subgroup Γ))
    (hW : W ≤ cenIn X {a}) (hWadm : Admits (A ⊔ cenIn X {a}) W) (hWA : cenIn W A = ⊥) :
    W = ⊥ := by
  rcases eq_or_ne X ⊥ with hX | hX
  · exact le_bot_iff.1 (hX ▸ hW.trans inf_le_left)
  · exact (Lemma214.Hyp.mk h hss hX ha ha1 hsolv hW hWadm hWA).eq_bot

end CFSG.SignalizerFunctorTheorem.McBride.Near
