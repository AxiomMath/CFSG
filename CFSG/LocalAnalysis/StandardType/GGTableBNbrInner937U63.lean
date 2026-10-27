module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSCrComp
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section U63

theorem ggTableBNbrInnerInputOn_937U63 (hU : GGUnitDvd63NbrRankInput) :
    GGTableBNbrInnerInputOn GGNbrInner937U63Label := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : GGNbrInner937U63Label p lab
  · refine ⟨hK, lab, hlab, ?_⟩
    have hSl0 := hSl
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := hSl
    dsimp only at ht hpn hl5 hp3
    subst ht hl5 hp3
    have hn : 1 ≤ n := hlab.1
    dsimp only [LargeEvenRawDatum] at hraw ⊢
    obtain ⟨K0, i1, i2, hK0, hs, hna, θ, hPθ⟩ := hraw
    refine ⟨K0, i1, i2, hK0, hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp => ?_⟩
    have hmark : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K := by
      refine ⟨hK, _, hlab, ?_⟩
      dsimp only [LargeEvenRawDatum]
      exact ⟨K0, i1, i2, hK0, hs, hna, θ, hSl0, hN, fun b hb =>
        ⟨_, hBsI b⁻¹ (Bs.inv_mem hb), largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))⟩⟩
    have hr := hU G 3 B Bs x L D J hcfg y K hnb hN hmark
    exact ggTableBNbrInner_of_card hcfg hnb hK θ hN hBsI hr
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hr)
      (U63TB.ggTorusNbrSCrK_unitary63 hK0 hn hpn) hYN hYK hYn hYp
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end U63

end CFSG.StandardType

end
