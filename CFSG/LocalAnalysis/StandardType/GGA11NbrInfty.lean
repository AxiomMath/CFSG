module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

theorem a11NbrInftyInput_holds : A11NbrInftyInput := by
  intro hL G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hz
  obtain ⟨hrest, _hcfg, hframe, hextra, _hcoh, _hrho⟩ := hctx
  obtain ⟨hGlue, _hrange, hnbK, _hBs, _hx, hy, _hD, _hnL, _hJK, _hJ9, _hLgen⟩ := hframe
  have hI : GGThmIHyp 7 B x L := hrest.1.1
  have hDJ : LargeEvenStdSub 7 B x L D J := hrest.1.2.2
  have hpJ : 7 ∣ Nat.card J := hextra.1
  have hy1 : y ≠ 1 := hnbK.1.2.2.1
  have hf3ord : orderOf (f 3) = 7 := hGlue.2.2.2.1 3
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers (f 3) := Subgroup.zpowers_le.mpr hy
  have hordy : orderOf y = 7 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp
      (hf3ord ▸ orderOf_dvd_of_mem_zpowers hy) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hyf : Subgroup.zpowers y = Subgroup.zpowers (f 3) :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hf3ord, hordy])
  exact (ggNbr_unique hL hI hDJ hpJ hnbK hnb (hyf.trans hz.symm)).symm

end CFSG.StandardType.A11

end
