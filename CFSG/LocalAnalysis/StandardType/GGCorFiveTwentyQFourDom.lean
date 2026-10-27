module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGRootGenSpOrthSplitAvoid

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGExcReflTBInputQFourOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGInnerDiagOnLabel S p Bs L →
        ∀ [Fact p.Prime], Nonempty (GGExcReflTBData p Bs L J)

@[expose] def GGRootGenLInputOnQFour (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGInnerDiagOnLabel S p Bs L → GGRootCompGenAvoiding p Bs L

@[expose] def GGRootGenNbrInputOnQFour (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
          GGRootCompGenAvoiding p Bs K

theorem GGExcReflTBInputQFourOn.toNS (h : GGExcReflTBInputQFourOn GGLabQFour) :
    GGExcReflTBInputNS :=
  fun G _ _ p B Bs x L D J hH hq hN _ => h G p B Bs x L D J hH hq hN hq

theorem GGRootGenLInputOnQFour.toNS {S : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour S) : GGRootGenLInputOnNS S :=
  fun G _ _ p B Bs x L D J hH hq hN _ hL => h G p B Bs x L D J hH hq hN hL

theorem GGRootGenNbrInputOnQFour.toNS {S : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour S) : GGRootGenNbrInputOnNS S :=
  fun G _ _ p B Bs x L D J hH hq hN _ y K hnb hK => h G p B Bs x L D J hH hq hN y K hnb hK

private theorem normalizer_of_tb_rootGen_qFour (hL : GGLBalanceInput)
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

private theorem rootGenL_qFour_of_open
    (hRig : GGLabelRigidInput)
    (h : GGRootGenLInputOnQFour fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQFour p Bs L)
    (hN : GGNbrLabelsOk p B Bs x D J) : GGRootCompGenAvoiding p Bs L := by
  rcases GGInnerDiagOnLabel.typeA_or (ggInnerDiagOnLabel_phiOneTwo_L hRig hHyp) with hA | hO
  · exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidTypeA_holds hHyp
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hA)
  · rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSpOrthSplitLabel p lab ∨
        (GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab))
        (fun lab hlab => (em (GGRootGenSpOrthSplitLabel p lab)).imp_right fun hn => ⟨hlab, hn⟩)
        hO).elim_or with h₁ | h₂
    · exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_spOrthSplit hHyp h₁
    · exact h _ p B Bs x L D J hHyp hq hN h₂

private theorem rootGenNbr_qFour_of_open
    (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGRootGenNbrInputOnQFour fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQFour p Bs L)
    (hN : GGNbrLabelsOk p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    GGRootCompGenAvoiding p Bs K := by
  rcases GGInnerDiagOnLabel.typeA_or (ggInnerDiagOnLabel_phiOneTwo_nbr hRig hraw hiso hHyp hN hnb)
    with hA | hO
  · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidTypeA_holds hHyp hnb
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hA)
  · rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSpOrthSplitLabel p lab ∨
        (GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab))
        (fun lab hlab => (em (GGRootGenSpOrthSplitLabel p lab)).imp_right fun hn => ⟨hlab, hn⟩)
        hO).elim_or with h₁ | h₂
    · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_spOrthSplit hHyp hnb h₁
    · exact h _ p B Bs x L D J hHyp hq hN y K hnb h₂

theorem ggCorFiveTwentyQFourReflFailNonSplitInput_of_qFour
    (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hTB : GGExcReflTBInputQFourOn GGLabQFour)
    (hL : GGRootGenLInputOnQFour fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab)
    (hK : GGRootGenNbrInputOnQFour fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab) :
    GGCorFiveTwentyQFourReflFailNonSplitInput := by
  intro G _ _ p B Bs x L D J hHyp hq hN _ _
  haveI : Fact p.Prime := ⟨hHyp.1.1.2.2.2.2.2.1.1⟩
  obtain ⟨T⟩ := hTB G p B Bs x L D J hHyp hq hN hq
  exact normalizer_of_tb_rootGen_qFour hLB hP hHyp T (rootGenL_qFour_of_open hRig hL hHyp hq hN)
    fun y K hnb => rootGenNbr_qFour_of_open hRig hraw hiso hK hHyp hq hN hnb

end CFSG.StandardType

end
