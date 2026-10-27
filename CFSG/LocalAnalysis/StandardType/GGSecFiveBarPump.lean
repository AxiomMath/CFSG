module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFive_bar_pump_L
    (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs) ∧ ggAutomizer J Bs ≤ ggAutomizer L Bs := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
  exact ⟨(hPump.1 G p B Bs x L D J 𝒦 hcfg hsplit).1, ggAutomizer_mono Bs hJL⟩

theorem ggSecFive_bar_pump_nbr
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧ ggAutomizer J Bs ≤ ggAutomizer K Bs := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  have hJK : J ≤ K := le_of_ggNbr hL hconf.1 hconf.2.2 hpJ hnb
  exact ⟨(hPump.2 G p B Bs x L D J 𝒦 hcfg hsplit y K hnb).1, ggAutomizer_mono Bs hJK⟩

end CFSG.StandardType

end
