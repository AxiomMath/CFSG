module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSporB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.Sporadic.Ru


theorem rowOK_of_isSporadic_Ru {X : Type} [Group X] [Finite X] (h : IsSporadic .Ru X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_Ru h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) := fam_ru_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 14 * 8906625 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_Ru.trans (by norm_num)
  have hmems : ∀ r ∈ ruMems, r.order = 2 ^ 14 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases ru_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
