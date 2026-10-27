module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowSporBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutSpor
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.Sporadic.He


theorem rowOK_of_isSporadic_He {X : Type} [Group X] [Finite X] (h : IsSporadic .He X) :
    RowOK X := by
  have hout := CFSG.Quasithin.H23Out.out5Pow_of_isSporadic_He h
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) := fam_he_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv]
    exact fam_he_order.1.trans (by norm_num)
  have hmems : ∀ r ∈ heMems, r.order = 2 ^ 10 ∨ 3 ∣ r.order := by decide +kernel
  refine rowOK_of_rows hX (by norm_num) (by norm_num) (by norm_num) hcard ?_ hout
  intro T Y hT hTY
  rcases he_overgroups ⟨e⟩ hT hTY with hY | ⟨r, hr, hord, -, -⟩
  · exact Or.inl hY
  · exact Or.inr (by rw [hord]; exact hmems r hr)

end CFSG.Quasithin.H23P4
