module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeCF
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBNbrInnerInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I _ θ => S p lab →
          (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) →
          ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({y} : Set G) →
            Y ≤ Subgroup.normalizer (Bs : Set G) → Y ≤ Subgroup.normalizer (K : Set G) →
            Subgroup.centralizer (Bs : Set G) ≤ Y →
            (∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
              ∀ g ∈ Y, n * g * n⁻¹ ∈ Y) →
            (∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
            ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G)

theorem GGTableBNbrInnerInputOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBNbrInnerInputOn S') :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  exact largeEvenMarking_mono (fun lab _ _ _ _ _ h' => ⟨h'.1, fun hS => h'.2 (hSS' p lab hS)⟩)
    (h G p B Bs x L D J hcfg y K hnb hN P hP)

theorem GGTableBNbrInnerInputOn.or {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTableBNbrInnerInputOn S₁) (h₂ : GGTableBNbrInnerInputOn S₂) :
    GGTableBNbrInnerInputOn fun p lab => S₁ p lab ∨ S₂ p lab := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have h1 := h₁ G p B Bs x L D J hcfg y K hnb hN P hP
  have h2 := h₂ G p B Bs x L D J hcfg y K hnb hN _ h1
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h' =>
    ⟨h'.1.1, fun hS => hS.elim h'.1.2 h'.2⟩) h2

theorem GGTableBNbrInnerInputOn.of_cover {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → S p lab)
    (h : GGTableBNbrInnerInputOn S) : GGTableBNbrInnerInput := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := h G p B Bs x L D J hcfg y K hnb hN P hP
  refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hPθ, hQ⟩
  exact ⟨hs, hna, θ, hPθ, hQ (hS p lab hp hlab)⟩

theorem ggTableBNbrInnerInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, r, hlift, hT⟩
    exact ⟨hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_ggTorusNbr hcfg hnb hK θ hN hBsI hlift hT hYN hYK hYn hYp⟩
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

theorem largeEvenLabelAll_torusNbr_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I :=
  (TypeA.largeEvenLabelAll_tableBIrred_typeA hp hlab h).mono fun _ _ _ _ ⟨r, h1, h2⟩ =>
    ⟨r, h1, ggTorusNbr_of_ggTorusIrred hp h2⟩

theorem ggTableBNbrInnerInputOn_typeA : GGTableBNbrInnerInputOn GGTypeALabel :=
  ggTableBNbrInnerInputOn_of_labels fun _ _ hp hlab h => largeEvenLabelAll_torusNbr_typeA hp hlab h

theorem ggTableBNbrInnerInput_of_rest (h : GGTableBNbrInnerInputOn GGCorFourTwoRestLabel) :
    GGTableBNbrInnerInput :=
  (ggTableBNbrInnerInputOn_typeA.or h).of_cover fun p lab _ _ => em (GGTypeALabel p lab)

theorem ggTableBNbrInnerInput_of_labels
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      GGCorFourTwoRestLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbr p r R I) :
    GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_rest (ggTableBNbrInnerInputOn_of_labels h)

theorem ggL44iiiNotInnerInput_of_rest (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) (hTBK : GGTableBNbrInnerInputOn GGCorFourTwoRestLabel) :
    GGL44iiiNotInnerInput :=
  ggL44iiiNotInnerInput_of_tableB hL hJp hI2 (ggTableBNbrInnerInput_of_rest hTBK)

theorem ggL44iiiMarkingInput_of_rest (hBN : GGBstarNbrNormalInput) (hgr : GGNbrGraphInput)
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput) (hlang : GGRawFieldConjInput)
    (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput) (hI2 : GGStdSubBstarMeetInput)
    (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput) (hTBM : GGTableBModuleInput)
    (hTBA : GGTableBActionInput) (hTBK : GGTableBNbrInnerInputOn GGCorFourTwoRestLabel)
    (hlax : GGNbrLangAxisInput) : GGL44iiiMarkingInput :=
  ggL44iiiMarkingInput_of_tableB hBN hgr hraw hcen hlang hL hJp hI2 hTB hNN hTBM hTBA
    (ggTableBNbrInnerInput_of_rest hTBK) hlax

end CFSG.StandardType

end
