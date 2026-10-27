module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrQTwoQFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveA11ConfigWide {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  p = 7 ∧ Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 ∧
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1

theorem GGSecFiveA11Config.toWide {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (h : GGSecFiveA11Config p B Bs x L D J) :
    GGSecFiveA11ConfigWide p B Bs x L D J := by
  obtain ⟨hp, hL, y, K, hnb, hK, -⟩ := h
  exact ⟨hp, hL, y, K, hnb, hK⟩

@[expose] def GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      ¬ GGNbrLabelsOk p B Bs x D J → ¬ GGSecFiveA11Config p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGCorFiveTwentyA11CfgInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGSecFiveA11ConfigWide p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGCorFiveTwentyA11CfgTBInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGSecFiveA11ConfigWide p B Bs x L D J →
        ∀ [Fact p.Prime], Nonempty (GGExcReflTBData p Bs L J)

@[expose] def GGCorFiveTwentyA11CfgRootGenLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGSecFiveA11ConfigWide p B Bs x L D J → GGRootCompGenAvoiding p Bs L

@[expose] def GGCorFiveTwentyA11CfgRootGenNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGSecFiveA11ConfigWide p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGRootCompGenAvoiding p Bs K

theorem GGCorFiveTwentyInputNbrQTwoQFour.noA11Cfg (h : GGCorFiveTwentyInputNbrQTwoQFour) :
    GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg :=
  fun G _ _ p B Bs x L D J hH hq hN _ => h G p B Bs x L D J hH hq hN

private theorem ggCorFiveTwentyNormalizer_of_tb_rootGen (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) [Fact p.Prime]
    (T : GGExcReflTBData p Bs L J) (hLg : GGRootCompGenAvoiding p Bs L)
    (hKg : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGRootCompGenAvoiding p Bs K) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs :=
    ggAutomizer_mono Bs (hHyp.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left)
  have hE : ∃ ρ : MulAut ↥Bs, ∀ t : MulAut ↥Bs, GGIsReflection p t → t ∈ ggAutomizer ⊤ Bs →
      (∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) → t = ρ := by
    by_cases hex : ∃ t : MulAut ↥Bs, GGIsReflection p t ∧ t ∈ ggAutomizer ⊤ Bs ∧
        ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t
    · obtain ⟨ρ, hρ, hρA, hρc⟩ := hex
      exact ⟨ρ, fun t ht htA htc => T.unique hp2 hHyp.2.2.2.1 hJL ht htA htc hρ hρA hρc⟩
    · exact ⟨1, fun t ht htA htc => absurd ⟨t, ht, htA, htc⟩ hex⟩
  obtain ⟨ρ, hρ⟩ := hE
  have hG0 : GGHypCompInG0 p B Bs x L D J := by
    refine ⟨ρ, fun t Jt htρ hr hind hJC hpc => ?_⟩
    by_contra hJt
    refine htρ (hρ t hr ?_ ?_)
    · obtain ⟨g, -, hgN, hg⟩ := hind
      exact mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top g, hgN, hg⟩
    · exact commutes_ggAutNormalClosure_of_not_le hp (le_ggG0_left p B x L D J)
        (fun t Jt hr hind hJC hpc => ggDichotomy_of_hyp hL hP hHyp hr hind hJC hpc) hr hind hJC
        hpc hJt
  exact normalizer_le_normalizer_ggG0 hp hG0 hLg hKg

theorem ggCorFiveTwentyA11CfgInput_of_rootGen (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hTB : GGCorFiveTwentyA11CfgTBInput) (hLg : GGCorFiveTwentyA11CfgRootGenLInput)
    (hKg : GGCorFiveTwentyA11CfgRootGenNbrInput) : GGCorFiveTwentyA11CfgInput := by
  intro G _ _ p B Bs x L D J hHyp hq hA
  haveI : Fact p.Prime := ⟨hHyp.1.1.2.2.2.2.2.1.1⟩
  obtain ⟨T⟩ := hTB G p B Bs x L D J hHyp hq hA
  exact ggCorFiveTwentyNormalizer_of_tb_rootGen hL hP hHyp T (hLg G p B Bs x L D J hHyp hq hA)
    (hKg G p B Bs x L D J hHyp hq hA)

theorem GGCorFiveTwentyInputNbrQTwoQFour.of_a11Cfg (hA : GGCorFiveTwentyA11CfgInput)
    (hR : GGCorFiveTwentyInputNbrQTwoQFourNoA11Cfg) : GGCorFiveTwentyInputNbrQTwoQFour := by
  intro G _ _ p B Bs x L D J hH hq hN
  by_cases hD : GGSecFiveA11Config p B Bs x L D J
  · exact hA G p B Bs x L D J hH hq hD.toWide
  · exact hR G p B Bs x L D J hH hq hN hD

end CFSG.StandardType
