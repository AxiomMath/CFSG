module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumO

import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace Insp7

theorem numFactAt_m11
    : NumFactAt M11Fam := by
  refine numFactAt_of_not_dvd_aut (fun L _ _ _ ⟨e⟩ hdvd => ?_)
  have hcard : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have hcen : Subgroup.center (NativeSporadic.Carrier .M11) = ⊥ :=
    CFSG.Sporadic.Schreier.m11_center_eq_bot'
  have hA : Nat.card (MulAut L) ≤ 7920 := by
    have h : Nat.card (MulAut (NativeSporadic.Carrier .M11)) ≤
        Nat.card (NativeSporadic.Carrier .M11) := CFSG.Sporadic.Schreier.m11_mulAut_card
    rw [hcard] at h
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact h
  have hZ : Subgroup.center L = ⊥ := by
    have h1 : (Subgroup.center L).map e.toMonoidHom = Subgroup.center (NativeSporadic.Carrier .M11) :=
      Subgroup.map_center_eq e
    rw [hcen] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hL : Nat.card L = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcard
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conj_eq_center, hZ]
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  have hB : Nat.card L ≤ Nat.card (MulAut L) := Nat.card_le_card_of_injective _ hinj
  have hC : Nat.card (MulAut L) = 7920 := by omega
  rw [hC] at hdvd
  exact absurd hdvd (by decide)

end Insp7

end CFSG.Quasithin
