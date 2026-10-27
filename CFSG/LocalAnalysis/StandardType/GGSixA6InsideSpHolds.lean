module

public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTransport
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpStepThree
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpStepFour
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpStepFive
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComb
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpSep
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall

public section

namespace CFSG.StandardType

namespace A6InsideSp

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem core_holds : Core := by
  intro K _ _ _ n hK hn B Lx D J x hB hB4 hLx hx1 hcyc hpre hA6
  obtain ⟨E, hBE, hE, hEsc⟩ := exists_elemAbelian_le_selfCentralizing Nat.prime_three hB
  obtain ⟨L, _, _, _, ζ, hL, hζo, ⟨F⟩⟩ := exists_frame_two hK hE hEsc
  haveI : NeZero n := ⟨by omega⟩
  have hsn : F.s = n := s_eq F hL
  have hxB : x ∈ B := hpre.1 hpre.2.2.2.1
  obtain ⟨c, rfl⟩ := F.mem_tor x (hBE hxB)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 F.tor_zero
  have hJ : Nat.card J = 360 := by
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, IOneOrthEnd.card_alternatingGroup_six]
  have h27 : ¬ 27 ∣ Nat.card J := by
    rw [hJ]
    norm_num
  obtain ⟨i₀, hci, rfl⟩ :=
    exists_single_and_eq_spFixedFactor F hK hζo hL (by omega) hc hBE hLx hcyc hpre h27
  obtain ⟨a, b, d, ha, hb, -, hd, hdB, hs6, hker, hsurj⟩ :=
    exists_shape F hK hζo hL hci hBE hB4 hpre hJ
  rcases exists_pair_or_separating (fun f => F.tor f ∈ B)
      (fun f g hf hg => by
        rw [F.tor_add hζo.pow_eq_one]
        exact mul_mem hf hg)
      (fun k f hf => by
        rw [tor_smul F hζo.pow_eq_one]
        exact pow_mem hf _)
      ha hb hxB hdB hci hd hker hsurj with ⟨d', hd'B, hd'0, hd', h3, hker'⟩ | hsep
  · exact Or.inl (exists_not_small F hK hζo hL hs6 hci hBE hxB hd'B hd'0 hd' h3 hker')
  · exact Or.inr fun U _ hU hBU => eq_bot_of_separating F hK hζo hL (by omega) hsep hU hBU

end A6InsideSp

theorem ggSixA6InsideSpKnown_holds : GGSixA6InsideSpKnown :=
  A6InsideSp.ggSixA6InsideSpKnown_of_core A6InsideSp.core_holds

end CFSG.StandardType
