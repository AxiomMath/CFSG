module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameLine
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin

section NbrType

variable {G : Type} [Group G] [Finite G]

theorem ggSpNbr_automizer_card_ge_of_type (hlift : GGSpLiftInput) (hMp : GGInnerDiagMpInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K')
    (hType : StatedClassicalModel (K' ⧸ Subgroup.center K') .PSp (m + 1) 2 f) :
    2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K' Bs) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hm1 : 1 ≤ m := by
    have := hN.2.1
    omega
  have hrankLB : p ^ (m + 1 + 1) ≤ Nat.card Bs := by
    rw [(ggSpConfig_rank_orders hlift hMp hcfg hInn hN).1]
  obtain ⟨φ₀, hφ₀inj, hφ₀range⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  have hinnerL : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp hm1 hN.1.1 hInn.1 φ₀ hφ₀inj hφ₀range
  have hnormL : Bs ≤ Subgroup.normalizer (L : Set G) := hInn.1.le_normalizer
  have hZL : Subgroup.center L = ⊥ := by
    have := center_range_statedSp_eq_bot φ₀ hφ₀inj
    rwa [hφ₀range] at this
  have hcentL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    hcfg.card_bstar_centralizer_le
  have hmarkK' : GGInnerDiagOn Bs K' := hInn.2 y' K' hK'
  obtain ⟨φK', hφK'inj, hφK'range⟩ := hlift G K' (m + 1) f hN.2.1 hmarkK'.1 hType
  have hinnerK' : ∀ b ∈ Bs, ∃ g ∈ K', ∀ k ∈ K', b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp hm1 hN.1.1 hmarkK' φK' hφK'inj hφK'range
  have hnormK' : Bs ≤ Subgroup.normalizer (K' : Set G) := hmarkK'.le_normalizer
  have hZK' : Subgroup.center K' = ⊥ := by
    have := center_range_statedSp_eq_bot φK' hφK'inj
    rwa [hφK'range] at this
  have hcentK' : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) ≤ p :=
    card_bstar_centralizer_le_of_lifts hp hp2 (Nat.succ_pos m) hBs φ₀ hφ₀inj hφ₀range hZL hnormL
      hinnerL φK' hφK'inj hφK'range hZK' hnormK' hinnerK' hcentL hrankLB
  exact two_pow_mul_factorial_le_card_ggAutomizer_of_lift hp hp2 h2 φK' hφK'inj hBs hφK'range
    hnormK' hinnerK' hcentK' hrankLB

end NbrType

end CFSG.StandardType
