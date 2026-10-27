module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLE7Det
public import CFSG.LocalAnalysis.StandardType.GGQ2InLE7D6

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

theorem inLCoverAtFrame_excRaw_E7 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) (hC : InLLeafOrSelCases (excRaw 4)) :
    GGQ2InLCoverAtFrame (excRaw 4) := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb hF
  subst hp
  obtain ⟨real⟩ := hF
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  obtain ⟨hyx, hxy, hyBs, ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent,
    hjcomp, hins, hnorm, hvx0, hUfin, hxU⟩ :=
    ggQ2CensusFrame_setup real hS hI1 hxBs hnb
  obtain ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK, hcandK, hvyU, hvyx⟩ :=
    ggQ2CensusFrame_caseDCand real hLB hP hS hI1 hxBs hnb hyx hxy hyBs hjadm hjcomp
  rcases hC _ hvx0 ℓ hℓadm (codeL_label_q2 hrig real hS hℓadm hℓcomp) hℓocc hℓcent
      (hvxℓ.mpr hxL) _ hUfin hxU j hjadm hjocc hjcent hins hnorm _ hvyU hvyx k hcandK hinsJK with
    hleaf | hD6 | hDet
  · obtain ⟨W, hWL, hWK, hfixx, hfixy, hleaf⟩ := hleaf
    have hLlin : (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) =
        W.toLin.parab {i | i ≠ W.a} := by
      rw [hWL, ← real.normalizer_eq ℓ hℓadm, hℓcomp]
    have hKlin : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
        W.toLin.parab {i | i ≠ W.b} := by
      rw [hWK, ← real.normalizer_eq k hkadm, hkcomp]
    exact Or.inl ⟨GGQ2Lin.toModel (p := 3) (by norm_num) W.toLin real.coord hxBs hyBs hLlin
      hKlin hfixx hfixy, hleaf⟩
  · exact Or.inr (Or.inl (ggQ2InL_selD6_of_raw hLB hP hS hI1 real hnb hyBs hjadm hjcomp hkadm
      hkcent hkcomp hD6))
  · exact Or.inr (Or.inr (ggQ2InL_selDet_of_raw hLB hP hS hI1 real hnb hyBs hkadm hkcent hkcomp
      hDet))

end CFSG.StandardType.GGQ2Frame

end
