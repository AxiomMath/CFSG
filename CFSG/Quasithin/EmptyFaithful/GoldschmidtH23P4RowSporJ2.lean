module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSporB
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporJ2

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Quasithin.H13.NQCore
open CFSG.Sporadic.J2


theorem rowOK_of_isSporadic_J2 {X : Type} [Group X] [Finite X] (h : IsSporadic .J2 X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_J2 h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) := fam_j2_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 7 * 4725 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_J2.trans (by norm_num)
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  exact j2_overgroups_card ⟨e⟩ hT hTY

end CFSG.Quasithin.H23P4
