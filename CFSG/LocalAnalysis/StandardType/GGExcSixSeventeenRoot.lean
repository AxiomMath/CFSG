module

public import CFSG.LocalAnalysis.StandardType.GGExcCorootComponent
public import CFSG.LocalAnalysis.StandardType.GGLatFixedRootExc
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenLeft

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section SixSeventeen

theorem sixSeventeenRootWitnessLeft_exc_of_stdForm (hreg : GGExcRegimeInput)
    (hstd : GGSixExcStandardFormInput) (hcoroot : GGLatCorootExc) (hfix : GGLatFixedRootExc)
    (t : StatedLieTag) (ht : GGExcFive t) :
    GGSixSeventeenRootWitnessInputForLeft fun t' => t' = t := by
  intro G _ _ p B Bs x L D J t' n f ψ ht' _hne hctx s1 b L₁ hpair
  subst t'
  obtain ⟨hbB, hb1, hL₁comp, hnex⟩ := hpair
  have hp := hctx.prime
  have hp2 := hctx.ne_two
  obtain ⟨S, π, F, hS, hπ, hπ1, -, -, -, hF5⟩ :=
    hstd G p B Bs x L D J t n f ψ ht hctx s1
      (hreg G p B Bs x L D J t n f ψ ht hctx s1)
  have hbne : (⟨b, hbB⟩ : Bs) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨O, hOrb, hnsolv, hcent, -, hfixmem, hsc⟩ :=
    F.comp_all ⟨b, hbB⟩ hbne L₁ hL₁comp
  have hsingle : IsSingleComp S
      (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (F.coord ⟨b, hbB⟩))) O := by
    rcases hsc with hs | hk
    · exact hs
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr hk)))) hnex
  obtain ⟨γ, hγO, hγroots, hγπ⟩ :=
    hfix t f ht S π hS hπ hπ1 p (Multiplicative.toAdd (F.coord ⟨b, hbB⟩))
      (F.coord_fixed ⟨b, hbB⟩) O hOrb hsingle
  obtain ⟨hcspan, hcπ, hcne, -⟩ := hcoroot t f ht S π hS hπ p hp hp2 γ hγroots hγπ
  obtain ⟨e', he'⟩ := F.coord_surj (corootCoord p S γ) hcspan hcπ
  have he'L : (e' : G) ∈ L₁ := hfixmem γ hγO hγπ e' he'
  obtain ⟨he'1, L₂, hL₂comp, hL₂card⟩ :=
    exists_component_of_coroot hcoroot t f ht p hp hp2 Bs (ggG0 p B x L D J) S π hS hπ F γ
      hγroots hγπ 1 (fun h => hp.ne_one (ZMod.one_eq_zero_iff.mp h)) e'
      (by rw [one_smul]; exact he')
  exact ⟨(e' : G), he'L, e'.2, fun h => he'1 (Subtype.coe_injective h), L₂, hL₂comp, hL₂card⟩

theorem sixSeventeenRootWitnessExc_of_stdForm (hreg : GGExcRegimeInput)
    (hstd : GGSixExcStandardFormInput) (hcoroot : GGLatCorootExc) (hfix : GGLatFixedRootExc) :
    GGSixSeventeenRootWitnessExcTagsLeft :=
  ⟨sixSeventeenRootWitnessLeft_exc_of_stdForm hreg hstd hcoroot hfix .F4 (Or.inl rfl),
    sixSeventeenRootWitnessLeft_exc_of_stdForm hreg hstd hcoroot hfix .E6 (Or.inr (Or.inl rfl)),
    sixSeventeenRootWitnessLeft_exc_of_stdForm hreg hstd hcoroot hfix .E7
      (Or.inr (Or.inr (Or.inl rfl))),
    sixSeventeenRootWitnessLeft_exc_of_stdForm hreg hstd hcoroot hfix .E8
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    sixSeventeenRootWitnessLeft_exc_of_stdForm hreg hstd hcoroot hfix .twistedE6
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

end SixSeventeen

end CFSG.StandardType
