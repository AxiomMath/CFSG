module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSpor
public import CFSG.Quasithin.Vol2.KGFactAutSylowM11

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Quasithin.H13.KGSporLat
open CFSG.Sporadic.Mathieu


theorem rowOK_of_isSporadic_M11 {X : Type} [Group X] [Finite X] (h : IsSporadic .M11 X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_M11 h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) := fam_m11_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 4 * 495 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_M11.trans (by norm_num)
  have hmems : ∀ r ∈ m11Mems, r.order = 2 ^ 4 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases m11_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
