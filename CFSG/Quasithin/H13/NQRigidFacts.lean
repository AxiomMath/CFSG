module

public import CFSG.Quasithin.H13.NQBlockWitnessSingleton
public import CFSG.Quasithin.SteinbergBTQuasisimpleSQTKCenter
public import CFSG.Quasithin.H13.NQSetupNonscalar
public import CFSG.Quasithin.H13.NQTermComponentPair
public import CFSG.Quasithin.H13.NQBlockOddRankOne
public import CFSG.Quasithin.H13.NQCatQuasisimpleJ4
public import CFSG.Quasithin.H13.NQRigidConjugate

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)
open scoped MatrixGroups Pointwise

section TwoLocal

variable {G : Type} [Group G]

theorem isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal {M : Subgroup G} :
    CFSG.IsMaximalTwoLocal M ↔ quasithinIsMaxTwoLocal M := by
  constructor
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun H hH hMH => ?_⟩
    by_contra hne
    exact hmax H (lt_of_le_of_ne hMH (Ne.symm hne)) hH
  · rintro ⟨hM, hmax⟩
    exact ⟨hM, fun H hMH hH => hMH.ne (hmax H hH hMH.le).symm⟩

theorem maximalTwoLocalsContaining_eq_singleton {Y M : Subgroup G}
    (hM : quasithinIsMaxTwoLocal M) (hYM : Y ≤ M)
    (huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → Y ≤ M' → M' = M) :
    CFSG.maximalTwoLocalsContaining (Y : Set G) = {M} := by
  ext M'
  simp only [CFSG.maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hM', hsub⟩
    exact huniq M' (isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal.mp hM')
      (SetLike.coe_subset_coe.mp hsub)
  · rintro rfl
    exact ⟨isMaximalTwoLocal_iff_quasithinIsMaxTwoLocal.mpr hM, SetLike.coe_subset_coe.mpr hYM⟩

end TwoLocal

@[expose] def FactWitnessSingleton : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ → NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      IsFrattiniIrreducible X L →
      CFSG.maximalTwoLocalsContaining ((X ⊔ T : Subgroup G) : Set G) = {M}

theorem factWitnessSingleton_of_inputs
    (hProd : NQBlock.OriginalXTNormalComponent)
    (hL3 : NQBlock.OriginalWitnessExcludesCrossLinearThree)
    (hSp4 : NQBlock.OriginalWitnessExcludesEvenSymplecticFour) : FactWitnessSingleton := by
  intro G _ _ T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  obtain ⟨hM, hle, huniq⟩ := NQBlock.original_characteristic_witness_singleton_of_inputs hProd
    hL3 hSp4 h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  exact maximalTwoLocalsContaining_eq_singleton hM hle huniq

@[expose] def FactCenterOddPart : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → CFSG.SectionRank.IsSQTKCat J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (center J)

theorem factCenterOddPart_holds :
    FactCenterOddPart :=
  fun _ _ _ hJ hK p hp hp5 => (SteinbergBT.quasisimple_SQTK_center_odd_part hJ hK).2 p hp hp5

@[expose] def FactOuterPrime : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → CFSG.SectionRank.IsSQTKCat J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.pRank p (Outer J) ≤ 1

theorem factOuterPrime_holds :
    FactOuterPrime :=
  fun J _ _ hJ hK p hp hp5 =>
    (NQCat.sqtk_quasisimple_cyclic_large_prime_outer_sylows J hJ hK p hp hp5).2

@[expose] def FactSimpleQuotientSQT : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X → ∀ (N : Subgroup X) [N.Normal],
    IsSimpleGroup (X ⧸ N) → (∃ a b : X ⧸ N, a * b ≠ b * a) →
    CFSG.IsStronglyQuasithin (X ⧸ N) ∧ CFSG.Blueprint.Catalog (X ⧸ N)

theorem factSimpleQuotientSQT_holds :
    FactSimpleQuotientSQT := by
  intro X _ _ hX N _ hS hnab
  set e : ((⊤ : Subgroup X) ⧸ N.subgroupOf ⊤) ≃* X ⧸ N :=
    QuotientGroup.congr (N.subgroupOf ⊤) N Subgroup.topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, mem_top x⟩, hx, rfl⟩) with he
  have : IsSimpleGroup ((⊤ : Subgroup X) ⧸ N.subgroupOf ⊤) := e.isSimpleGroup
  have hnab' : ∃ a b : (⊤ : Subgroup X) ⧸ N.subgroupOf ⊤, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨hsqt, hcat⟩ := CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hX ⊤
    (N.subgroupOf ⊤) hnab'
  refine ⟨fun r hr hr2 => ?_, (CFSG.SectionRank.catalog_congr e).mp hcat⟩
  rw [← pRank_congr hr.one_lt e]
  exact hsqt r hr hr2

@[expose] def FactQuadraticOffender : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (L : Subgroup (Module.End (ZMod 2) W)ˣ), CFSG.IsQuasisimple L →
    (repOfSubgroup L).IsIrreducible → CFSG.Blueprint.Catalog (L ⧸ center L) →
    (∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (L ⧸ center L) ≤ 1) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ D : Subgroup (L ⧸ center L), Nat.card D = p →
    ∀ T : Sylow 2 (L ⧸ center L),
      (D : Set (L ⧸ center L)) * (T : Set (L ⧸ center L)) =
        (T : Set (L ⧸ center L)) * (D : Set (L ⧸ center L)) →
    ∀ B : Subgroup (Module.End (ZMod 2) W)ˣ, CFSG.IsElementaryAbelian 2 B → B ≠ ⊥ →
      B ≤ normalizer (L : Set (Module.End (ZMod 2) W)ˣ) →
      (∀ a ∈ B, ∀ b ∈ B, ∀ w : W, (b.val - 1) ((a.val - 1) w) = 0) →
      Nat.card W ≤ Nat.card B * Nat.card {w : W // ∀ b ∈ B, b.val w = w} →
      ∃ f : ℕ, 3 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ f ∧
        Nonempty ((L ⧸ center L) ≃* SL(2, F))

theorem factQuadraticOffender_holds :
    FactQuadraticOffender := by
  intro W _ _ _ _ L hLq hirr hcat hodd p hp hp5 D hD T hDT B hBe hB1 hBN hquad hoff
  obtain ⟨-, f, hf, F, hFf, hFt, hF, -, -, -, -, -, -, -, -, θbar, -⟩ :=
    NQBlock.odd_rank_one_catalog_quadratic_offender_forces_even_linear_natural_module L hLq hirr
      hcat hodd hp hp5 D hD T hDT B hBe hB1 hBN hquad hoff
  exact ⟨f, hf, F, hFf, hFt, hF, ⟨θbar⟩⟩

@[expose] def FactThinCentralQuotient : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsSQTKCat H → ∀ J : Subgroup H,
    CFSG.IsComponent J → ∀ h : H, CFSG.conjugate J h ≠ J →
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (J ⧸ center J) ≤ 1

theorem factThinCentralQuotient_holds :
    FactThinCentralQuotient :=
  fun _ _ _ hH _ hJ _ hh => NQTerm.SQTK_conjugate_component_pair_thin_central_quotient hH hJ hh

@[expose] def FactNonscalarG2Triality : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → 5 ≤ p → ∀ (D : Subgroup H) (Q : Sylow 2 H),
    (Q : Subgroup H) ≤ D → ∀ (K : Subgroup H) [K.Normal] (X : Subgroup H), X ≤ D →
    (X.subgroupOf D).Normal → X ≤ K → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    (∃ γ ∈ ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map (normalizerFrattiniConj X),
      ¬ ∃ c : ZMod p, ∀ w, γ w = w ^ c.val) →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    (∀ f : ℕ, 2 ≤ f → ¬ CFSG.Blueprint.ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f) ∧
      ∀ f : ℕ, 1 ≤ f → ¬ CFSG.Blueprint.ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f

theorem factNonscalarG2Triality_holds :
    FactNonscalarG2Triality :=
  fun _ _ _ _ hp hp5 _ Q hQD _ _ _ hXD hXn hXK hXA hns hZ =>
    NQSetup.nonscalar_original_local_sylow_prime_action_excludes_even_G2_and_triality_quotients
      hp hp5 Q hQD hXD hXn hXK hXA hns hZ

@[expose] def FactLargeRee : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → ∀ (D : Subgroup H)
    (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) (K : Subgroup H) [K.Normal] (X : Subgroup H),
    X ≤ D → ∀ hDX : D ≤ normalizer (X : Set H), X ≤ K → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
    ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) →
    (∃ a : ℕ, 1 ≤ a ∧ CFSG.Blueprint.ReeTitsModel
      ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .twistedF4 2 (2 * a + 1)) →
    ∀ q (hq : q ∈ (Q : Subgroup H)), normalizerFrattiniConj X ⟨q, hDX (hQD hq)⟩ = 1

theorem factLargeRee_holds :
    FactLargeRee := by
  intro H _ _ p hp hp2 D Q hQD K _ X hXD hDX hXK hP hZ hS
  have : Fact p.Prime := ⟨hp⟩
  exact (NQBlock.large_Ree_normal_quotient_forces_local_Sylow_centralization_of_prime_witness hp2
    Q hQD hXD hDX hXK hP hZ hS).2

end CFSG.Quasithin.H13.NQRigid
