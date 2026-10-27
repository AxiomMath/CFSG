module

public import CFSG.Quasithin.Background.C1GNC128
import CFSG.Foundations.KCoreClosure
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def TheoremC126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
    IsGNChoice C₁ C₂ → C126Statement C₁ C₂

@[expose] def TheoremC127 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C127Statement (G := G)

@[expose] def TheoremC127ND : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T P K : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → CFSG.SectionRank.IsKGroupCat ↥X →
    P ∈ uFamHat X T → IsBlock2 P K → ⁅K, thompsonJ T⁆ = K → P = T ⊔ conjClosure K T →
    ¬ K ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) →
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n)

@[expose] def TheoremC127Degenerate : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T P K : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → CFSG.SectionRank.IsKGroupCat ↥X →
    P ∈ uFamHat X T → IsBlock2 P K → ⁅K, thompsonJ T⁆ = K → P = T ⊔ conjClosure K T →
    K ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) →
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n)

theorem theoremC127_iff_nondegenerate_and_degenerate :
    TheoremC127 ↔ TheoremC127ND ∧ TheoremC127Degenerate := by
  constructor
  · intro h
    exact ⟨fun G _ _ X T P K hX hT hKG hP hK hc hgen _ =>
      h G X T P K hX hT hKG hP hK hc hgen,
      fun G _ _ X T P K hX hT hKG hP hK hc hgen _ =>
      h G X T P K hX hT hKG hP hK hc hgen⟩
  · rintro ⟨hND, hDeg⟩ G _ _ X T P K hX hT hKG hP hK hc hgen
    by_cases hcentral : K ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G)
    · exact hDeg G X T P K hX hT hKG hP hK hc hgen hcentral
    · exact hND G X T P K hX hT hKG hP hK hc hgen hcentral

@[expose] def TheoremC123Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
    IsGNChoice C₁ C₂ → C123TwoStatement C₁ C₂

@[expose] def TheoremC19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], DistinctBlocksCommuteStatement (G := G)

@[expose] def TheoremC116Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BaumNormalizesChiBlocksStatement (G := G)

@[expose] def TheoremB42Alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], AltBlockStatement (G := G)

section Members

variable {G : Type} [Group G] [Finite G]

theorem kGroup_of_forall_commute {A : Type} [Group A] [Finite A] (h : ∀ a b : A, a * b = b * a) :
    CFSG.SectionRank.IsKGroupCat A :=
  CFSG.KCore.KGroupAllSimple.of_commutative CFSG.SectionRank.catalog_containsAbelianSimple h

theorem inM_facts (hsimple : IsSimpleGroup G) (hqtke : quasithinIsQTKECat G) {T M : Subgroup G}
    (hsyl : quasithinIsSylowTwo T) (hM : InM T M) :
    CharTwo M ∧ IsSQTKTC M ∧ IsSylowTwoOf T M := by
  have hTM : T ≤ M := hM.2
  have hSylM : IsSylowTwoOf T M :=
    ⟨hTM, hsyl.1, fun h => hsyl.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hsyl
  have hMchar : CharTwo M := hqtke.2.1 M hM.1.1 ⟨S, hS ▸ hTM⟩
  have hO : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  refine ⟨hMchar, ⟨?_, stronglyQuasithin_of_pCoreOf_ne_bot hqtke hO⟩, hSylM⟩
  by_cases hnab : ∃ a b : G, a * b ≠ b * a
  · exact kGroup_of_pCoreOf_ne_bot hqtke hsimple hnab hO
  · push Not at hnab
    exact kGroup_of_forall_commute fun a b => Subtype.ext (hnab a b)

end Members

theorem gNCampbellC128_of (h118 : TheoremC118) (h126 : TheoremC126) (h127 : TheoremC127)
    (h123 : TheoremC123Two) (h19 : TheoremC19) (h116 : TheoremC116Two) (hB42 : TheoremB42Alt)
    (hF36 : A36Facts) (hF38 : A38Facts) : GNCampbellC128 := by
  intro G _ _ T hsimple hqtke hsyl hT0
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T hsyl.1 hT0
  refine ⟨C₁ T, C₂ T, h1ne, h1Z, h1char, h2ne, h2B, h2char, fun M hM => ?_⟩
  obtain ⟨hMchar, hMsq, hSylM⟩ := inM_facts hsimple hqtke hsyl hM
  exact C1GN.lemma_C128 hC (h126 G C₁ C₂ hC) (h127 G) (h123 G C₁ C₂ hC) (h19 G) (h116 G)
    (hB42 G) hMchar hMsq (C1GN.a38Part3_quotient hF36 hF38 hMsq) hSylM hT0

end CFSG.Quasithin
