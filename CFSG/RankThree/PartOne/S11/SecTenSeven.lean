module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Assembly.CatalogTransport
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint.NativeSporadic (IsSporadic)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_singleton_ne_top_of_simple [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {c : G} (hc : c ≠ 1) :
    Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have hcen : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({c} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hc hcen
  · obtain ⟨a, b, hab⟩ := hnonab
    have : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

omit [Finite G] in
theorem inCatalog_quotient_center_of_quasisimple [IsSimpleGroup G] (hKP : CFSG.IsKProper G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {c : G} (hc : c ≠ 1) {L : Subgroup G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hq : CFSG.IsQuasisimple L) :
    InCatalog (L ⧸ Subgroup.center L) := by
  have hne : L ≠ ⊤ := fun htop =>
    centralizer_singleton_ne_top_of_simple hnonab hc (top_le_iff.mp (htop ▸ hLc))
  have hK := hKP L hne
  let e0 : (⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
  let e : ((⊤ : Subgroup L) ⧸ Subgroup.center (⊤ : Subgroup L)) ≃* (L ⧸ Subgroup.center L) :=
    QuotientGroup.congr _ _ e0 (Subgroup.map_center_eq e0)
  have hs : IsSimpleGroup ((⊤ : Subgroup L) ⧸ Subgroup.center (⊤ : Subgroup L)) :=
    e.isSimpleGroup_congr.mpr hq.2.1
  obtain ⟨i, ⟨φ⟩⟩ := hK ⊤ (Subgroup.center (⊤ : Subgroup L)) hs
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

theorem catalog_quotient_center_of_quasisimple [IsSimpleGroup G] (hKP : CFSG.IsKProper G)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {c : G} (hc : c ≠ 1) {L : Subgroup G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hq : CFSG.IsQuasisimple L) :
    Catalog (L ⧸ Subgroup.center L) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  exact hbridge _ hq.2.2 (inCatalog_quotient_center_of_quasisimple hKP hnonab hc hLc hq)

theorem mem_classicalTags_of_statedClassicalModel {T : Type} [Group T] {t : StatedLieTag}
    {n ℓ f : ℕ} (h : StatedClassicalModel T t n ℓ f) : t ∈ classicalTags := by
  have := CFSG.Milestones.statedClassicalModel_tag_mem T t n ℓ f h
  simpa [classicalTags] using this

theorem maximal_moving_plane_data (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G} (hL : L ∈ sectionTenZeroStar p A) :
    ∃ (E : Subgroup (MulAut (L ⧸ Subgroup.center L))) (U : Subgroup (L ⧸ Subgroup.center L)),
      PlaneOn p E U ∧ ¬ PlaneCentralizes E U := by
  obtain ⟨hAL, U, hpl, e, he, u, hu, hmove⟩ := moving_maximal_plane_witness hS h hL
  exact ⟨_, U, hpl, fun hc => hmove (hc e he u hu)⟩

@[expose] def MaximalMovingOddClassicalExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, ∀ (t : StatedLieTag) (n ℓ f : ℕ), t ∈ classicalTags →
      ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ¬ StatedClassicalModel (L ⧸ Subgroup.center L) t n ℓ f

@[expose] def MaximalMovingEvenOrSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A,
      EvenLieType (L ⧸ Subgroup.center L) ∨ NativeSporadic.SporadicRep (L ⧸ Subgroup.center L)

@[expose] def MaximalMovingEvenOrFiveSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A,
      EvenLieType (L ⧸ Subgroup.center L) ∨ IsSporadic (L ⧸ Subgroup.center L) .Co1 ∨
        IsSporadic (L ⧸ Subgroup.center L) .J4 ∨ IsSporadic (L ⧸ Subgroup.center L) .Ly ∨
        IsSporadic (L ⧸ Subgroup.center L) .Suz ∨ IsSporadic (L ⧸ Subgroup.center L) .HN

@[expose] def MaximalMovingEvenOrThreeSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A,
      EvenLieType (L ⧸ Subgroup.center L) ∨ IsSporadic (L ⧸ Subgroup.center L) .Co1 ∨
        IsSporadic (L ⧸ Subgroup.center L) .J4 ∨ IsSporadic (L ⧸ Subgroup.center L) .HN

@[expose] def MaximalMovingEvenOrJ4HN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A,
      EvenLieType (L ⧸ Subgroup.center L) ∨ IsSporadic (L ⧸ Subgroup.center L) .J4 ∨
        IsSporadic (L ⧸ Subgroup.center L) .HN

@[expose] def MaximalMovingEvenOrHN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A,
      EvenLieType (L ⧸ Subgroup.center L) ∨ IsSporadic (L ⧸ Subgroup.center L) .HN

theorem maximalMovingOddClassicalExcluded_of (hS : SchreierFor InCatalog)
    (hodd : ActualCoverOddClassicalPlaneCentralization) : MaximalMovingOddClassicalExcluded := by
  intro G _ _ p A h L hL t n ℓ f ht hℓ hℓ2 hf hmodel
  obtain ⟨hq, -⟩ := moving_maximal_quasisimple_data hS h hL
  obtain ⟨E, U, hpl, hnc⟩ := maximal_moving_plane_data hS h hL
  exact hnc (hodd G h.2.2.2.2.1.le L hq t n ℓ f ht hℓ hℓ2 hf hmodel p E U hpl)

theorem maximalMovingEvenOrSporadic_of (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hodd : MaximalMovingOddClassicalExcluded)
    (halt : ActualCoverAlternatingPlaneCentralization) (hG2 : ActualCoverOddG2PlaneCentralization)
    (hF4 : OddF4ActualCoverLocalRankFour) (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (hhigh : ActualCoverHigherExceptionalSmallFieldRestrictions)
    (htri : CharThreeTrialityActualCoverLocalRankFour)
    (hree : SmallReeActualCoverNoLargePrimeAutomorphismPlane) : MaximalMovingEvenOrSporadic := by
  intro G _ _ p A h L hL
  obtain ⟨hq, hAL, c, hcA, hc1, hLc, hcard⟩ := moving_maximal_quasisimple_data hS h hL
  obtain ⟨E, U, hpl, hnc⟩ := maximal_moving_plane_data hS h hL
  have hG3 : CFSG.twoLocalOddRank G ≤ 3 := h.2.2.2.2.1.le
  have hLcent : L ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := hq.2.2
  have hcat : Catalog (L ⧸ Subgroup.center L) := by
    have := h.1
    exact catalog_quotient_center_of_quasisimple h.2.2.1 hbridge h.2.1 hc1 hLcent hq
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  rcases hcat with ⟨q, hqp, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | hcl | hex | hsp
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · exact absurd (halt G hG3 L n hn ⟨φ⟩ p E U hpl) hnc
  · left
    obtain ⟨t, n, ℓ, f, hmodel⟩ := hcl
    by_cases hℓ : ℓ = 2
    · subst hℓ
      exact ⟨t, n, f, hmodel.1, Or.inl ⟨mem_classicalTags_of_statedClassicalModel hmodel, hmodel⟩⟩
    · exact absurd hmodel (hodd G p A h L hL t n ℓ f
        (mem_classicalTags_of_statedClassicalModel hmodel) hmodel.1.1 hℓ hmodel.1.2.1)
  · left
    rcases hex with ⟨t, ℓ, f, ht, hmodel⟩ | ⟨t, ℓ, f, ht, hmodel⟩ | ⟨ℓ, f, hmodel⟩
    ·
      by_cases hℓ : ℓ = 2
      · subst hℓ
        exact ⟨t, 0, f, hmodel.1, Or.inr (Or.inl ⟨rfl, ht, hmodel⟩)⟩
      · exfalso
        have hprime : ℓ.Prime := hmodel.1.1
        have hf : 1 ≤ f := hmodel.1.2.1
        have ht' : t = .G2 ∨ t = .F4 ∨ (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) ∨
            t = .trialityD4 := by
          simpa [chevalleyExceptionalTags, or_assoc] using ht
        rcases ht' with rfl | rfl | hEt | rfl
        · exact hnc (hG2 G hG3 L ℓ f hprime hℓ hf hmodel p E U hpl)
        · have := (hF4 G L ℓ f hprime hℓ hf hmodel).2.2
          omega
        · exact hℓ (hE G hG3 L ℓ f hprime hf t hEt hmodel).2.1
        · rcases (hhigh G hG3 L ℓ f hprime hf .trialityD4 (by simp) hmodel).2.2.1 rfl with h2 | h3
          · exact hℓ h2
          · subst h3
            have := (htri G L f hmodel).2.2
            omega
    ·
      have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
        simpa [reeTitsTags, or_assoc] using ht
      rcases ht' with rfl | rfl | rfl
      · exfalso
        obtain ⟨-, -, hnoplane⟩ := hree G hG3 L ℓ f hmodel
        exact (hnoplane p hp hp3).2 E hpl.elementary hpl.card
      · have hadm := hmodel.1
        simp only [StatedLieAdmissible] at hadm
        obtain ⟨-, -, -, h2, -⟩ := hadm
        subst h2
        exact ⟨.twistedF4, 0, f, hmodel.1, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hmodel⟩))⟩
      · have hadm := hmodel.1
        simp only [StatedLieAdmissible] at hadm
        obtain ⟨-, -, -, h2, -⟩ := hadm
        subst h2
        exact ⟨.Tits, 0, f, hmodel.1, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hmodel⟩))⟩
    ·
      obtain ⟨hp2, a, ha, K, _, _, hf, hK, hiso⟩ := hmodel
      subst hp2
      refine ⟨.twistedB2, 0, f, ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, hf⟩, by omega⟩,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ⟨rfl, a, ha, K, inferInstance, inferInstance, hf, hK,
          hiso⟩⟩))⟩
  · exact Or.inr hsp

theorem maximalMovingEvenOrFiveSporadic_of (hS : SchreierFor InCatalog)
    (h0 : MaximalMovingEvenOrSporadic)
    (hres : ActualCoverSporadicMovingPlaneFiveModelResidual) : MaximalMovingEvenOrFiveSporadic := by
  intro G _ _ p A h L hL
  rcases h0 G p A h L hL with hev | hsp
  · exact Or.inl hev
  · obtain ⟨hq, -⟩ := moving_maximal_quasisimple_data hS h hL
    obtain ⟨E, U, hpl, hnc⟩ := maximal_moving_plane_data hS h hL
    exact Or.inr (hres G h.2.2.2.2.1.le L hq hsp p E U hpl hnc)

theorem maximalMovingEvenOrThreeSporadic_of (hS : SchreierFor InCatalog)
    (h1 : MaximalMovingEvenOrFiveSporadic) (hly : LyLargePrimePlaneCentralization)
    (hsuz : SuzLargePrimePlaneCentralization) : MaximalMovingEvenOrThreeSporadic := by
  intro G _ _ p A h L hL
  obtain ⟨hq, -⟩ := moving_maximal_quasisimple_data hS h hL
  obtain ⟨E, U, hpl, hnc⟩ := maximal_moving_plane_data hS h hL
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := hq.2.2
  rcases h1 G p A h L hL with hev | hco | hj4 | hLy | hSuz | hhn
  · exact Or.inl hev
  · exact Or.inr (Or.inl hco)
  · exact Or.inr (Or.inr (Or.inl hj4))
  · exact absurd (hly _ hsimple hnab hLy p E U hpl).2 hnc
  · exact absurd (hsuz _ hsimple hnab hSuz p E U hpl).2 hnc
  · exact Or.inr (Or.inr (Or.inr hhn))

theorem maximalMovingEvenOrJ4HN_of (h2 : MaximalMovingEvenOrThreeSporadic)
    (hco1 : Co1ActualArbitraryCentralCoversForceTwoLocalRankFour) : MaximalMovingEvenOrJ4HN := by
  intro G _ _ p A h L hL
  rcases h2 G p A h L hL with hev | hco | hj4 | hhn
  · exact Or.inl hev
  · exfalso
    have h4 := hco1 G L (L ⧸ Subgroup.center L) (QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _) hco (by rw [QuotientGroup.ker_mk'])
    have h3 : CFSG.twoLocalOddRank G ≤ 3 := h.2.2.2.2.1.le
    omega
  · exact Or.inr (Or.inl hj4)
  · exact Or.inr (Or.inr hhn)

theorem maximalMovingEvenOrHN_of (hS : SchreierFor InCatalog) (h3 : MaximalMovingEvenOrJ4HN)
    (hj4 : J4LargePrimePlaneCentralization) : MaximalMovingEvenOrHN := by
  intro G _ _ p A h L hL
  obtain ⟨hq, -⟩ := moving_maximal_quasisimple_data hS h hL
  obtain ⟨E, U, hpl, hnc⟩ := maximal_moving_plane_data hS h hL
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := hq.2.2
  rcases h3 G p A h L hL with hev | hJ4 | hhn
  · exact Or.inl hev
  · exact absurd (hj4 _ hsimple hnab hJ4 p E U hpl) hnc
  · exact Or.inr hhn

theorem inSec10Seven_of_even_or_HN (h4 : MaximalMovingEvenOrHN)
    (hhn : MaximalMovingComponentHNQuotientsExcluded) : InSec10Seven := by
  intro G _ _ p A h L hL
  rcases h4 G p A h L hL with hev | hHN
  · exact hev
  · exact absurd hHN (hhn G p A h L hL)

theorem inSec10Seven_of_inspections (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hI : TenSevenInspections) : InSec10Seven :=
  inSec10Seven_of_even_or_HN
    (maximalMovingEvenOrHN_of hS
      (maximalMovingEvenOrJ4HN_of
        (maximalMovingEvenOrThreeSporadic_of hS
          (maximalMovingEvenOrFiveSporadic_of hS
            (maximalMovingEvenOrSporadic_of hS hbridge
              (maximalMovingOddClassicalExcluded_of hS hI.oddClassical) hI.alternating hI.oddG2
              hI.oddF4 hI.eType hI.higherExceptional hI.charThreeTriality hI.smallRee)
            hI.sporadicResidual) hI.ly hI.suz) hI.co1) hI.j4) hI.hn

end CFSG.RankThree.PartOne
