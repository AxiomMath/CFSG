module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandFourteen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Notation

variable {G : Type} [Group G]

abbrev GGRCSNbar (r : G) : Type :=
  ↥(Subgroup.centralizer ({r} : Set G)) ⧸
    CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))

noncomputable abbrev ggRCSImg (r : G) (Y : Subgroup G) : Subgroup (GGRCSNbar r) :=
  (Y.subgroupOf (Subgroup.centralizer ({r} : Set G))).map
    (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))))

end Notation

section Inputs

@[expose] def GGRootCentSummandStructInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ 𝒮 : Set (Subgroup (GGRCSNbar r)),
          (∀ S ∈ 𝒮, GGRCSQuasiPiece p (ggRCSImg r (ggM p B x L D J)) S ∨
            (p = 3 ∧ GGRCSSThreePiece (ggRCSImg r (ggM p B x L D J)) S)) ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ sSup 𝒮

@[expose] def GGRootCentSThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r → p = 3 →
        ∀ S : Subgroup (GGRCSNbar r), GGRCSSThreePiece (ggRCSImg r (ggM p B x L D J)) S →
          ∃ R : Subgroup (GGRCSNbar r), R.Normal ∧
            IsPGroup p ↥(R.map (QuotientGroup.mk' (LargeEvenPPrimeCore p (GGRCSNbar r)))) ∧
            S ≤ R

@[expose] def GGRootCentAutKIIIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKIII (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

@[expose] def GGRootCentAutKIVInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKIV p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

@[expose] def GGRootCentAutKNotExcInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKNotExc p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixRootCentralizerSummandInput_of_parts (hSch : SchreierFor InCatalog)
    (hstr : GGRootCentSummandStructInput) (hS3 : GGRootCentSThreeInput)
    (h3 : GGRootCentAutKIIIInput) (h4 : GGRootCentAutKIVInput)
    (hexc : GGRootCentAutKNotExcInput) : GGSixRootCentralizerSummandInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨𝒮, h𝒮, hcov⟩ := hstr G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hEr := hch.le_centralizer
  obtain ⟨hEel, hEc⟩ := ggBarE_elem_card hp hp2 hEr hch.2.1
  have hEc' := hEc.trans hch.2.2.1
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := hch.2.2.2.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hNtop := ggStepTwo_centralizer_ne_top hctx.1.2.1 hr1
  have hKP : KProper InCatalog G := hctx.1.2.2.1
  have hO2 := ggRCS_pCore_two_quot_eq_bot ↥(Subgroup.centralizer ({r} : Set G))
  have hOut : ∀ K : Subgroup (GGRCSNbar r), CFSG.IsComponent K →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => ggRCS_outer_solvable hKP hSch hNtop _ hK
  refine ⟨𝒮, fun S hS => ?_, hcov⟩
  rcases h𝒮 S hS with hQ | ⟨hp3, hS3'⟩
  · right
    obtain ⟨K, hK, hSK⟩ := ggRCS_exists_component hp2 hO2 hOut hfus hEel hEc' hQ
    have hKp : p ∣ Nat.card K := hQ.choose_spec.2.2.2.1.trans (Subgroup.card_dvd_of_le hSK)
    have hKc : IsComponentOf K ⊤ := ⟨le_top, (ggAssemblyIsSubnormal_iff le_top).mpr
      hK.2.subgroupOf,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hK.1⟩
    have hKO : ¬ K ≤ (QuotientGroup.mk' (LargeEvenPPrimeCore p (GGRCSNbar r))).ker := by
      rw [QuotientGroup.ker_mk']
      intro hle
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp CFSG.pPrimeCore_coprime_card
        (hKp.trans (Subgroup.card_dvd_of_le hle))
    have hKimg := ggIsComponentOf_map _ hKc hKO
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hKimg
    refine ⟨K, hSK, hKimg, fun hKV => ?_⟩
    have hEK := ggLemmaThreeThirteen_top hfus hEel hEc' hK hKp hKV
    have hset : GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S :=
      ⟨hK, hKV, hEK, hSK, hQ⟩
    exact ⟨hK, ggRCS_autKConfig hp hfus hEel hEc' hEK hK
      (ggRCS_inCatalog_center_quot hKP hNtop _ hK) hQ hSK
      (h3 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)
      (h4 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)
      (hexc G p B Bs x L D J t n f ψ hctx s1 s2 E r hch K S hset)⟩
  · left
    exact hS3 G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hp3 S hS3'

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepThreeBInput_of_parts (hcyc : GGRootCentralizerCyclicInput)
    (hKF : GGKGroupFusionLayerInput) (hSch : SchreierFor InCatalog)
    (hstr : GGRootCentSummandStructInput) (hS3 : GGRootCentSThreeInput)
    (h3 : GGRootCentAutKIIIInput) (h4 : GGRootCentAutKIVInput)
    (hexc : GGRootCentAutKNotExcInput) : GGSixStepThreeBInput :=
  ggSixStepThreeBInput_of_summands hcyc hKF
    (ggSixRootCentralizerSummandInput_of_parts hSch hstr hS3 h3 h4 hexc)

end Inputs

end CFSG.StandardType
