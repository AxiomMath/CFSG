module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanARowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPhanA5Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatPhanA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggSecFiveCompat_of_phanARow
    (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanA5Input) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hrow : GGSecFivePhanARow p B Bs x L D J) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨𝒦, hcfg, hns, ι, M, e, hpres, ⟨m, σ, hm, hM⟩, hbig⟩ := hrow
  obtain ⟨f, hf4, θ, hker, hrange, hG0, hmark, hP⟩ :=
    ggSecFivePhanA_marked hL1 hRk1 hGen hOrb hL2 hPair hNbr hJ hcfg hns hpres σ hm hM hbig
  obtain ⟨ψ₀, hpres₀, hcompat⟩ :=
    ggSecFiveCompatPhanA_of_marks hNS hL1 hcfg hns hpres σ hm hM hbig hf4 θ hker hrange hG0 hmark hP
  exact ⟨.PSU, m + 1, f, ψ₀, hpres₀, L, Or.inl rfl, hcompat⟩

theorem ggSecFiveCompatRestWResInput_of_phanARow
    (hN : GGSecFiveCompatRestWResNInput) (hNS : GGSecFiveNSKGPosAInput)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hJ : GGSecFiveJoinPhanA5Input) :
    GGSecFiveCompatRestWResInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL hReg
  by_cases hrow : GGSecFivePhanARow p B Bs x L D J
  · exact ggSecFiveCompat_of_phanARow hNS hL1 hRk1 hGen hOrb hL2 hPair hNbr hJ hrow
  · exact hN G p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL hReg hrow

end CFSG.StandardType

end
