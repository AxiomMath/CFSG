module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Split

variable {G : Type} [Group G] [Finite G]

theorem ggTorusTBGroup_of_L {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) :
    GGTorusTBGroup p r R I L (ggQuotHom θ) (ggGamma L hN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
  exact ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hL, hA, hAI, hr, h3,
    ggTorusSelfCent_ggGamma hN hSC⟩

theorem ggReflGenerated_of_split_L (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    (hCP : GGLabelCenterPCyclicInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hsp : LargeEvenMarking ↥L fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) :
    GGReflGenerated p (ggAutomizer L Bs) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hInnL : GGInnerDiagOn Bs L := hHyp.2.2.1.1
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnL
  obtain ⟨R, _, θ, I, r, hBsI, hlift, hT⟩ :=
    exists_weylDatum_of_halfSplit hTB hRig hcfg hInnL hsp hN
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  exact ggReflGenerated_of_weylReflSet hp hp2 hBs hSC hHyp.2.2.2.1 hN
    (ggNbr_card_center_le_of_centerPCyclic hCP hcfg hInnL)
    (hT L (ggQuotHom θ) (ggGamma L hN).range (ggTorusTBGroup_of_L hcfg hInnL.1 θ hN hBsI hlift))

theorem ggNbrReflGen_of_split_hyp (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    (hCP : GGLabelCenterPCyclicInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) :
    GGReflGenerated p (ggAutomizer K Bs) :=
  ggNbrReflGen_of_halfSplit hTB hRig hHyp.1 hHyp.2.2.2.1 hnb (hHyp.2.2.1.2 y K hnb) hsp
    (ggNbr_card_center_le_of_centerPCyclic hCP hHyp.1 (hHyp.2.2.1.2 y K hnb))

end Split

@[expose] def GGCorFiveTwentyAllSplit {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)

theorem ggCorFiveTwentyReflDom_of_allSplit (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (h : GGCorFiveTwentyAllSplit p B x L D J) :
    GGCorFiveTwentyReflDom p B Bs x L D J :=
  ⟨ggReflGenerated_of_split_L hTB hRig hCP hHyp h.1,
    fun y K hnb => ggNbrReflGen_of_split_hyp hTB hRig hCP hHyp hnb (h.2 y K hnb)⟩

@[expose] def GGCorFiveTwentyQFourReflFailNonSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → ¬ GGCorFiveTwentyReflDom p B Bs x L D J →
        ¬ GGCorFiveTwentyAllSplit p B x L D J →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggCorFiveTwentyQFourReflFailNonSplitInput_of_reflFail
    (h : GGCorFiveTwentyQFourReflFailInput) : GGCorFiveTwentyQFourReflFailNonSplitInput :=
  fun G _ _ p B Bs x L D J hH hq hN hD _ => h G p B Bs x L D J hH hq hN hD

theorem ggCorFiveTwentyQFourReflFailInput_of_nonSplit (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput)
    (h : GGCorFiveTwentyQFourReflFailNonSplitInput) : GGCorFiveTwentyQFourReflFailInput :=
  fun G _ _ p B Bs x L D J hH hq hN hD =>
    h G p B Bs x L D J hH hq hN hD fun hS =>
      hD (ggCorFiveTwentyReflDom_of_allSplit hTB hRig hCP hH hS)

theorem ggCorFiveTwentyQFourReflFailNonSplitInput_of_aggregate (h : GGCorFiveTwentyInput) :
    GGCorFiveTwentyQFourReflFailNonSplitInput :=
  fun G _ _ p B Bs x L D J hH _ _ _ _ =>
    h G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2

theorem ggCorFiveTwentyQFourReflFailNonSplitInput_of_nonWeyl
    (h : GGCorFiveTwentyQFourNonWeylInput) : GGCorFiveTwentyQFourReflFailNonSplitInput :=
  ggCorFiveTwentyQFourReflFailNonSplitInput_of_reflFail
    (ggCorFiveTwentyQFourReflFailInput_of_nonWeyl h)

theorem ggCorFiveTwentyQFourNonWeylInput_of_scalarFail_nonSplit (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hS : GGCorFiveTwentyQFourScalarFailInput)
    (hF : GGCorFiveTwentyQFourReflFailNonSplitInput) : GGCorFiveTwentyQFourNonWeylInput :=
  ggCorFiveTwentyQFourNonWeylInput_of_scalarFail_reflFail hRig hraw hiso hS
    (ggCorFiveTwentyQFourReflFailInput_of_nonSplit hTB hRig hCP hF)

end CFSG.StandardType

end
