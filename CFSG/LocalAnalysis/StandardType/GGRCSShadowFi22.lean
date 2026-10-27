module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowVacuity
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMain
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggShadow_fi22_component
    {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W) (hp : p = 5)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* TauCeti.SporadicName.Fi22.Group))
    (hrow : ∀ C : Subgroup W, CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
      LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1) :
    ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ ∧
      Nat.card (↥C ⧸ Subgroup.center ↥C) = 174182400 := by
  by_cases hcomp : ∃ C₀ : Subgroup W,
      CFSG.Assembly.IsComponentOf C₀ (H ⊓ CFSG.generalizedFitting W)
  · obtain ⟨C₀, hC₀⟩ := hcomp
    obtain ⟨hopen, hcard⟩ := ggShadow_open_of_isComponentOf hC₀
    obtain ⟨-, hlie⟩ :=
      CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_POmegaPlus (hrow C₀ hC₀)
    refine ⟨C₀.subgroupOf (H ⊓ CFSG.generalizedFitting W), hopen, ?_⟩
    rw [hcard, hlie]
    decide
  · exfalso
    subst hp
    haveI : Fact (Nat.Prime 5) := ⟨hyp.1.1⟩
    have hnc : ∀ C : Subgroup W,
        ¬ CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W) :=
      fun C hC => hcomp ⟨C, hC⟩
    obtain ⟨S, U, hU, hUne, hSU⟩ :=
      ggShadow_vacuity hperf hL (ggSeitzExc_not_dvd_index_flat hyp) hnc
    have hFi : CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting W) := he
    exact hUne
      (CFSG.AGLEmbedding.kFactFi22NoTwo ↥(CFSG.generalizedFitting W) hFi S U hU hSU)

end CFSG.StandardType
