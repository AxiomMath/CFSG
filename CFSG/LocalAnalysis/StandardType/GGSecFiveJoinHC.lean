module

public import CFSG.LocalAnalysis.StandardType.GGCentralQuotientEq
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestWOfIdent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section JoinHC

variable {G : Type} [Group G] [Finite G]

theorem ggJoin_le_ggG0 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h𝒦 : GGNbrSet p B x D J 𝒦) :
    L ⊔ ⨆ K ∈ 𝒦, K ≤ ggG0 p B x L D J := by
  refine sup_le (le_ggG0_left p B x L D J) ?_
  refine iSup₂_le ?_
  intro K hK
  obtain ⟨y, hy⟩ := h𝒦.2 K hK
  exact le_ggG0_of_ggNbr hy

theorem ggG0_eq_join_of_joinHC (hHC : GGSecFiveJoinHCInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  have hle : L ⊔ ⨆ K ∈ 𝒦, K ≤ ggG0 p B x L D J := ggJoin_le_ggG0 (Bs := Bs) hcfg.2.2.2.1
  have hcard := hHC G p B Bs x L D J 𝒦 hcfg t n f ψ hpres
  have hEq : L ⊔ ⨆ K ∈ 𝒦, K = ggG0 p B x L D J :=
    eq_of_le_of_card_centralQuotient_le hle hpres.2.2.1 hcard.ge
  exact hEq.symm

theorem ggSecFiveJoinHCInput_of_join (hJ : GGSecFiveJoinInput) : GGSecFiveJoinHCInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg t n f ψ hpres
  rw [hJ G p B Bs x L D J 𝒦 hcfg]

theorem ggSecFiveCompatRestWInput_of_identHC (hI : GGSecFiveIdentCompatInput)
    (hHC : GGSecFiveJoinHCInput) : GGSecFiveCompatRestWInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL
  have hR : GGSecFiveRestHyp p B Bs x L D J :=
    ⟨hcfg, hOp, hInn, hNT, hd, fun ⟨n', f', hs⟩ => hL hs.leviCase⟩
  obtain ⟨𝒦, hmax⟩ := exists_ggMaximalJoin hR hW.2
  have hcfg' : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := ⟨hR, hW.2, hL, hmax⟩
  obtain ⟨t', n', f', ψ', -, hpres', hcompat⟩ := hI G p B Bs x L D J 𝒦 hcfg'
  have hG0 := ggG0_eq_join_of_joinHC hHC hcfg' hpres
  rw [← hG0] at hpres'
  exact ⟨t', n', f', ψ', hpres', L, Or.inl rfl, hcompat⟩

end JoinHC

end CFSG.StandardType

end
