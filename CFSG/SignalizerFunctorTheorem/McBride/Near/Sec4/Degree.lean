module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.DegAdd

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {H : Type*} [Group H] [Finite H]

theorem deg_le_permDeg (hK : oStar H = ⊤) : deg H ≤ permDeg H := by
  obtain ⟨f, hf⟩ := exists_injective_permDeg (H := H)
  have hs : Group.IsSolvable (QuotientGroup.mk' (CFSG.solvableRadical H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact isSolvable_solvableRadical
  have h := Deg.permDeg_le_card (QuotientGroup.mk' (CFSG.solvableRadical H))
    (QuotientGroup.mk'_surjective _) hs (Deg.isSS_of_oStar_eq_top hK) f
    (by rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]; exact bot_le)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

theorem deg_add (hK : oStar H = ⊤) (N : Subgroup H) [N.Normal] :
    deg H = deg N + deg (H ⧸ N) :=
  Deg.deg_add_of_oStar hK N

end CFSG.SignalizerFunctorTheorem.McBride.Near
