module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndLabel
public import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB CFSG.Open

theorem bijective_ggAutomizerGammaHom_and_reflGenerated {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hTB : GGTorusTBGroup 3 r R I L (ggQuotHom θ) (ggGamma L hN).range)
    (hT : GGTorusReflGenW 3 r R I) :
    Function.Bijective (ggAutomizerGammaHom hN) ∧ GGReflGenerated 3 (ggAutomizer L Bs) := by
  classical
  obtain ⟨-, hBs, -, -, -⟩ := hR.1.tableB_facts
  have hNoTr : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hR.1.2.1.2.2.2
  have hKcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 3 := by
    simpa using hR.1.card_bstar_inf_centralizer_L
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := fun _ hy => ⟨hy.1.1, hy.2⟩
    exact (Subgroup.card_le_of_le hle).trans hKcard.le
  have hW := hT (↥L) (ggQuotHom θ) _ hTB
  have hcard := card_ggAutomizer_eq_gamma_of_weylReflSet Nat.prime_three (by norm_num) hBs hSC
    hNoTr hN hZ hW
  exact ⟨(ggAutomizerGammaHom_injective Nat.prime_three hBs hNoTr hN hZ).bijective_of_nat_card_le
      hcard.ge,
    ggReflGenerated_of_weylReflSet Nat.prime_three (by norm_num) hBs hSC hNoTr hN hZ hW⟩

end CFSG.StandardType.FrameRoute

end
