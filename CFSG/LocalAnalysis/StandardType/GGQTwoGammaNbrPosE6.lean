module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrRes
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner

public section

namespace CFSG.StandardType

open Module

@[expose] def GGQ2NbrE6Sel {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs : Subgroup G)
    (x y : G) (D L J K : Subgroup G) : Prop :=
  ∃ M : GGQTwoModel p Bs x y D L J K, ∃ e : Fin 6 ≃ M.ι,
    M.coxeter = CoxeterMatrix.E₆.reindex e ∧ M.a = e 1

@[expose] def GGQ2GammaNbrPosRestInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    ¬ GGQ2NbrE6Sel p Bs x y D L J K → ¬ GGQ2SelInner G p Bs y J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

@[expose] def GGQ2GammaNbrPosE6Cell : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    GGQ2NbrE6Sel p Bs x y D L J K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

theorem ggQ2_gammaNbrPosE6Cell_holds (hHeart : GGQ2HeartInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosE6Cell := by
  intro G _ _ p B Bs x L D J hS hp hI _ _ y K hnb _ _ hsel u _
  obtain ⟨M, e, hE, ha⟩ := hsel
  have hA := ggQ2_e6_automizer_le hHeart hLB hP hp hS (ggQ2_ajOfSetting hP h5 hS)
    (ggQ2_K1_of_I1 hLB hP hS.1 hI) hnb M e hE ha
  exact fun φ hφ _ => hA hφ

theorem ggQ2_gammaNbrPos_of_rest_cell (hr : GGQ2GammaNbrPosRestInput)
    (hc : GGQ2GammaNbrPosE6Cell) (hi : GGQ2GammaNbrPosNotInLOn GGQ2SelInner) :
    GGQ2GammaNbrPosInput := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hrow hleaf u hu
  by_cases hsel : GGQ2NbrE6Sel p Bs x y D L J K
  · exact hc hS hp hI hxL hnb hrow hleaf hsel hu
  · by_cases hin : GGQ2SelInner G p Bs y J K
    · exact hi hS hp hI hxL hnb hrow hleaf hin hu
    · exact hr hS hp hI hxL hnb hrow hleaf hsel hin hu

end CFSG.StandardType

end
