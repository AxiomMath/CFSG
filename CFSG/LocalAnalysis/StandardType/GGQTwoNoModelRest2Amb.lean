module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbOrbit
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoModelEngine
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoWeylA3Free

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem GGQTwoAmbModel.card_Bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (hbas : GGQTwoAmbBasis M) :
    Nat.card ↥Bs = p ^ Fintype.card M.ι := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
  have hcardV : Nat.card M.V = p ^ Module.finrank (ZMod p) M.V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M.V), Nat.card_zmod]
  have hcardM : Nat.card M.V = Nat.card ↥Bs := by
    calc Nat.card M.V = Nat.card (Additive ↥Bs) := (Nat.card_congr M.model.toEquiv).symm
      _ = Nat.card ↥Bs := Nat.card_congr Additive.toMul
  rw [← hcardM, hcardV, hbas.2]

theorem ggQ2_noModelRest2_of_amb (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hLN : GGLNoncyclicInput) (h5 : GGQTwoCentralizerInput)
    (h1x : GGQTwoXInLNbrModelInput) (hnode : GGQ2TwoNodeInput) (hA : GGQ2AmbModelInput)
    (hA3 : GGQTwoNoWeylA3Free) : GGQ2NoModelRest2Input := by
  intro G _ _ p _ hp B Bs x L D J hS hI hnomod y K hnb h1 h2 hW _ hC hΓ
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨y', K', hnb', hM⟩ := h1x G p B Bs x L D J hS hI hxL
    exact hnomod y' K' hnb' hM
  by_cases hrow : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))
  · obtain ⟨y', K', hnb', h⟩ := hrow
    exact hnode hp hS hI hnb' h
  obtain ⟨M, hbas, hnd, -⟩ := hA hS hp hI hxL hrow hnomod hnb h1 h2 hW
  have hA3' : Fintype.card M.ι = 4 → Nat.card (ggAutomizer L Bs) ≠ 24 := fun h4 =>
    hA3 G p B Bs x L D J hS (by rw [M.card_Bs hbas, h4])
  have hPo : GGQ2Orbit p B Bs x D J :=
    ggQ2_ambOrbit hp hLN hS hnb M hbas hnd hA3'
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 p B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI
  rcases hPo with hPo | hX
  · exact ggQ2_reduction hS hC hΓ hPo
  · exact ggQ2_lemmaX hLB hP hS hAJS hK1 hΓ hX

end CFSG.StandardType

end
