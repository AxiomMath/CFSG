module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate3951

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

@[expose] def GGLieModelMarkingInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 2 f →
    commutator X = ⊤ → LieModel (X ⧸ Subgroup.center X) t n 2 f →
      CFSG.Assembly.LargeEvenMarkingLegacy X (fun _ _ _ _ _ _ => True)

abbrev GGLieModelMarkingInputLegacy := GGLieModelMarkingInput

namespace Canonical
@[expose] def GGLieModelMarkingInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 2 f →
    commutator X = ⊤ → LieModel (X ⧸ Subgroup.center X) t n 2 f →
      CFSG.Assembly.LargeEvenMarking X (fun _ _ _ _ _ _ => True)
end Canonical

section Bridge

@[expose] def GGInnerDiagBridgeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → ∀ G₀ : Subgroup G, ψ.range = G₀ →
    ∀ P : LargeEvenMarkProp ↥G₀, CFSG.Assembly.LargeEvenMarkingLegacy ↥G₀ P →
      CFSG.Assembly.LargeEvenMarkingLegacy ↥G₀ (fun lab R _ I F θ => P lab R I F θ ∧
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
          (∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) ↔
            GGPsiInnerDiag (ggU t n f).D ψ c)

abbrev GGInnerDiagBridgeInputLegacy := GGInnerDiagBridgeInput

namespace Legacy
abbrev GGLieModelMarkingInput := CFSG.StandardType.GGLieModelMarkingInputLegacy
abbrev GGInnerDiagBridgeInput := CFSG.StandardType.GGInnerDiagBridgeInputLegacy
end Legacy

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem ggSixHypPre_of_v2Core (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (h : GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ) :
    GGSixHypPre p B Bs x L D J := by
  obtain ⟨hBs, hDJ, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩, ⟨hBsN, hVI⟩, hNB, hNBs⟩ := h
  have hm0 := hR1 _ t n f hadm hperf hmodel
  have hm1 := hR G t n f ψ hadm hrk hker _ hrange _ hm0
  refine ⟨hBs, hDJ, largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hBsN, fun b hb => ?_⟩) hm1,
    hNB, hNBs⟩
  exact (hP.2 b (hBsN hb)).mpr (hVI b hb)

theorem ggSixHyp_of_v2Core (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) (hI : GGThmIHyp p B x L)
    (h : GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ) : GGSixHyp p B Bs x L D J := by
  have hpre := ggSixHypPre_of_v2Core hR1 hR h
  exact ⟨⟨hpre.1.1, hpre.1.2.1, ha' G p B Bs x L D J hI hpre⟩, hpre.2.1, hpre.2.2.1,
    hpre.2.2.2.1, hpre.2.2.2.2⟩

theorem ggSixHyp_of_v2 (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) (hI : GGThmIHyp p B x L) (h : GGSixHypV2 p B Bs x L D J) :
    GGSixHyp p B Bs x L D J := by
  obtain ⟨t, n, f, ψ, h⟩ := h
  exact ggSixHyp_of_v2Core hR1 hR ha' hI h

@[expose] def GGSecOneFiveV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∃ Bs D J : Subgroup G, GGSixHypV2 p B Bs x L D J

@[expose] def GGSecSixV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∀ Bs D J : Subgroup G,
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ →
        Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
          GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))

theorem ggSecOneFiveInput_of_v2 (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) (h15 : GGSecOneFiveV2Input) : GGSecOneFiveInput := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst
  obtain ⟨Bs, D, J, h⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  exact ⟨Bs, D, J, ggSixHyp_of_v2 hR1 hR ha' ⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩ h⟩

theorem ggSecSixV2Input_of_ggSecSixInput (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) (ha' : GGBstarRankInput) (h6 : GGSecSixInput) :
    GGSecSixV2Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ h
  exact h6 G hnonab hK hchar he p hp B x L hS hst Bs D J
    (ggSixHyp_of_v2Core hR1 hR ha' ⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩ h)

end Bridge

section Skeleton

theorem inCatalog_of_ggSixV2Core (hHolt : HoltUniqueFixedPointSimple) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {U : Type} [Group U] {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} (hL : L ≠ ⊥)
    (h6 : GGSixHypV2Core p B Bs x L D J Δ t n f ψ)
    (hM : Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
      GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))) :
    InCatalog G := by
  rcases hM with hM | ⟨hne, r, hr, hfix, hT⟩
  · obtain ⟨-, -, -, -, ⟨-, hmodel⟩, -⟩ := h6
    have hN : (ggG0 p B x L D J).Normal := Subgroup.normalizer_eq_top_iff.mp hM
    have htop : ggG0 p B x L D J = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ggG0 p B x L D J) with h | h
      · exact absurd (le_bot_iff.mp (h ▸ (le_sup_left : L ≤ ggG0 p B x L D J))) hL
      · exact h
    have hc : InCatalog (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) :=
      inCatalog_of_lieModel_std _ hmodel
    have hZ : Subgroup.center ↥(ggG0 p B x L D J) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzG : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ ggG0 p B x L D J := htop ▸ Subgroup.mem_top g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
      rw [center_eq_bot_of_simple hnonab, Subgroup.mem_bot] at hzG
      exact Subgroup.mem_bot.mpr (Subtype.ext hzG)
    have e1 : G ≃* ↥(ggG0 p B x L D J) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    have e2 : ↥(ggG0 p B x L D J) ≃*
        ↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact inCatalog_of_mulEquiv (e1.trans e2) hc
  · exact inCatalog_of_unique_fixed hHolt hnonab hne hr hfix hT

theorem lc_gl_std_of_v2_inputs (hHolt : HoltUniqueFixedPointSimple) (h15 : GGSecOneFiveV2Input)
    (h6 : GGSecSixV2Input) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G := by
  obtain ⟨Bs, D, J, t, n, f, ψ, hsix⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  have hL : L ≠ ⊥ := ne_bot_of_isComponentOf' hS.2.2.2.1
  exact inCatalog_of_ggSixV2Core hHolt hnonab hL hsix
    (h6 G hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ hsix)

end Skeleton

end CFSG.StandardType
