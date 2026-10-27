module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSpor
public import CFSG.Quasithin.Vol2.KGFactAutSylowM12

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Quasithin.H13.KGSporLat
open CFSG.Sporadic.Mathieu


theorem rowOK_of_isSporadic_M12 {X : Type} [Group X] [Finite X] (h : IsSporadic .M12 X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_M12 h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) := fam_m12_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 6 * 1485 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_M12.trans (by norm_num)
  have hmems : ∀ r ∈ m12Mems, r.order = 2 ^ 6 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases m12_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
