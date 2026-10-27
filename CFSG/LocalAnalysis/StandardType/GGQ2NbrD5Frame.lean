module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPosCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModel
public import CFSG.LocalAnalysis.StandardType.GGD5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2LeafPair {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs : Subgroup G) (x y : G) (D L J K : Subgroup G) : Prop :=
  ∃ M : GGQTwoModel p Bs x y D L J K, ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0

@[expose] def GGQ2NbrD5Frame {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs : Subgroup G) (x y : G) (L J K : Subgroup G) : Prop :=
  ∃ M : GGQTwoAmbModel p Bs y x K (L ⊔ K), ∃ e : Fin 5 ≃ M.ι,
    (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) ∧ M.a = e 0 ∧
      (M.b = e 1 ∨ M.b = e 3 ∨ M.b = e 4) ∧
      LinearIndependent (ZMod p) M.coroot ∧
      Submodule.span (ZMod p) (Set.range M.coroot) = ⊤ ∧
      p ∣ Nat.card J ∧
      Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J))) ∧
      ggAutomizer J Bs = Subgroup.closure (M.simple '' {k : M.ι | k ≠ M.a ∧ k ≠ M.b}) ∧
      (∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹) ∧
      lup10d_SCData Bs J

@[expose] def GGQ2InLCoverInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    GGQ2LeafPair p Bs x y D L J K ∨ GGQ2SelD6 G p Bs y J K ∨ GGQ2SelDet G p Bs y J K

@[expose] def GGQ2ExtCoverInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2NbrE6Sel p Bs x y D L J K → ¬ GGQ2SelInner G p Bs y J K →
    ¬ GGQ2NbrAmbDSel p Bs x y L K → ¬ GGQ2SelDet G p Bs y J K →
    GGQ2NbrD5Frame p Bs x y L J K

@[expose] def GGQ2NbrD5GammaInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K → GGQ2NbrD5Frame p Bs x y L J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2GammaNbrPosInLResidual_of_cover (h : GGQ2InLCoverInput) :
    GGQ2GammaNbrPosInLResidualInput := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb _ hleaf hd6 hdet _ _ u _
  rcases h hS hp hI hxL hnb with hleafpair | hd6' | hdet'
  · obtain ⟨M, hM⟩ := hleafpair
    exact absurd hM (hleaf M)
  · exact absurd hd6' hd6
  · exact absurd hdet' hdet

theorem ggQ2GammaNbrPosRestDet_of_cover (hc : GGQ2ExtCoverInput) (hd : GGQ2NbrD5GammaInput) :
    GGQ2GammaNbrPosRestDetInput := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hrow hleaf hE6 hin hamb hdet u hu
  exact hd hS hp hI hnb (hc hS hp hI hxL hnb hrow hleaf hE6 hin hamb hdet) hu

end CFSG.StandardType

end
