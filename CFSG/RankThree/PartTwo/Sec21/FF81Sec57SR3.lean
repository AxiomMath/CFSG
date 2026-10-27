module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57KDefs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6ShortRoot
import CFSG.RankThree.PartTwo.Sec21.FF81Sec57E

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

section H6


theorem S57.tH_conj_aElt4 : Sec4.Item434SmallTwoIII.tH * aElt 4 * Sec4.Item434SmallTwoIII.tH⁻¹ = zH 1 * zH 2 ^ 2 := by
  rw [aElt, conj_vecElt wreathFacts_zH]
  show zH 0 ^ 0 * zH 1 ^ 1 * zH 2 ^ 2 = _
  rw [pow_zero, one_mul, pow_one]

theorem S57.card_cen_w_H6 : Nat.card (Cen (zH 1 * zH 2 ^ 2)) = 108 := by
  rw [← S57.tH_conj_aElt4, ← S57.map_conj_cen CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH (aElt 4),
    Subgroup.card_map_of_injective (MulAut.conj CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH).injective, Cen, ← centSub_eq, card_centSub]
  rfl

end H6


theorem kf_sp6ShortRoot3 : KF_Sp6ShortRoot3 := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB _ hmono s hs hs2 hs1 hsu hsw
  obtain ⟨f, hf, hfL, -, e1, e2, -⟩ :=
    Sp6SR.exists_hom_sH hL hb₁ hb₂ hb₃ hB hmono hs hs2 hs1 hsu hsw
  have h := Sp6Transv.card_map_inf_cen hf ⊤ (zH 1 * zH 2 ^ 2)
  rw [hfL, map_mul, map_pow, e1, e2, top_inf_eq] at h
  rw [h]
  exact S57.card_cen_w_H6

end CFSG.RankThree.PartTwo.Sec21.FF81
