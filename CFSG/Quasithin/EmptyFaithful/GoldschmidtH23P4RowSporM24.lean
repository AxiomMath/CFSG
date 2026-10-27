module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSpor
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Sporadic.Mathieu


theorem rowOK_of_isSporadic_M24 {X : Type} [Group X] [Finite X] (h : IsSporadic .M24 X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_M24 h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) := fam_m24_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 239085 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_M24.trans (by norm_num)
  have hmems : ∀ r ∈ m24Mems, r.order = 2 ^ 10 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases m24_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
