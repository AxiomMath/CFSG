module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2DCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import Certificates.Certificate117
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSQ2DU6Input_of_u62
    (hU : GGU62OuterDiagInput) : GGSecFiveNSQ2DU6Input := by
  intro hTB _ _ _ G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres hD hsix _ _ _ _ _ hlab
  have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x := by
    have hconf : GGConfig p B Bs x L D J := hcfg.1.1
    obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
    intro b hb
    exact hTB G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN
      (hcfg.2.1 y K' hN) (Or.inr hcfg.2.1) b hb
  obtain ⟨hcard, -⟩ := nsQ2U62_card_D hcfg hFix hlab hpres hD
  obtain ⟨K, _hf, _hfin, lab, m', θ, hK, _h4m, hmrank, hSide, hdvd, hperf, _hlab, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hlab (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr5⟩ := hSide
  change n = 1 at hn1
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn1
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  obtain ⟨r, hrA, hrefl, hr6⟩ :=
    ggNsq2_exists_rankOne hU hTB hcfg hK hdvd θ hperf hBsN hbs (fun _ => hcard.ge)
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    fun i j hij => GGIsWeylMatrixAD.le_three (Or.inr hD) i j hij
  have hcox : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrefl
  exact hsix r hrA hcox hr6

end CFSG.StandardType

end
