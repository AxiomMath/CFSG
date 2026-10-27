module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section CompatW

theorem ggSecFiveCompatRestWInput_of_ident (hI : GGSecFiveIdentCompatInput)
    (hJ : GGSecFiveJoinInput) : GGSecFiveCompatRestWInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL
  have hR : GGSecFiveRestHyp p B Bs x L D J :=
    ⟨hcfg, hOp, hInn, hNT, hd, fun ⟨n', f', hs⟩ => hL hs.leviCase⟩
  obtain ⟨𝒦, hmax⟩ := exists_ggMaximalJoin hR hW.2
  have hcfg' : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := ⟨hR, hW.2, hL, hmax⟩
  obtain ⟨t', n', f', ψ', -, hpres', hcompat⟩ := hI G p B Bs x L D J 𝒦 hcfg'
  have hG0 := hJ G p B Bs x L D J 𝒦 hcfg'
  rw [← hG0] at hpres'
  exact ⟨t', n', f', ψ', hpres', L, Or.inl rfl, hcompat⟩

end CompatW

end CFSG.StandardType

end
