module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSporB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS


theorem rowOK_of_isSporadic_HS {X : Type} [Group X] [Finite X] (h : IsSporadic .HS X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_HS h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) := fam_hs_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 9 * 86625 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_HS.trans (by norm_num)
  have hmems : ∀ r ∈ hsMems, r.order = 2 ^ 9 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases hs_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
