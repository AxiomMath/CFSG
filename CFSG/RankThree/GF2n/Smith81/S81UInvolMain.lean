module

public import CFSG.RankThree.GF2n.Smith81.S81U28
public import CFSG.RankThree.GF2n.Smith81.S81UClass
public import CFSG.RankThree.GF2n.Smith81.S81UInvol1
public import CFSG.RankThree.GF2n.Smith81.S81UInvol2
public import CFSG.RankThree.GF2n.Smith81.S81UInvol3
public import CFSG.RankThree.GF2n.Smith81.S81UTransport

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem u6InvolFactsStatement_holds : U6InvolFactsStatement := by
  intro F _ _ _ f hF h4 t ht2 ht1
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one _)
  obtain ⟨g, hg⟩ := exists_conj_tStd hσ hω ht2 ht1
  have hkey : ∀ s : SUid (unitaryInvolution F 2 f) 6, g⁻¹ * t * g = s → t = g * s * g⁻¹ := by
    intro s hs
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = g * s * g⁻¹ := by rw [hs]
  rcases hg with h | h | h
  · left
    rw [hkey (tSU1 hσ hω) (Subtype.ext h)]
    exact (involModel12_tSU1 hF h4 hω).conj hσ g
  · left
    rw [hkey (tSU2 hσ hω) (Subtype.ext h)]
    exact (involModel12_tSU2 hF h4 hω).conj hσ g
  · right
    rw [hkey (tSU3 hσ hω) (Subtype.ext h)]
    exact (involModel3_tSU3 hσ hω).conj hσ g

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 in
theorem smith28E3U_of_FE1
    (hFE1 : Smith24E3UUniformStatement) : Smith28E3UStatement :=
  smith28E3U_of_uniform hFE1 u6InvolFactsStatement_holds

end CFSG.RankThree.GF2n.Smith81
