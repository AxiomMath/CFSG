module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTag
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusTag
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny

namespace GGOppRadExc

theorem ggOppRadGood_of_surjective_subgroup {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : ∀ R : Subgroup G, R ≠ ⊥ → GGRadicalTwo C R → GGOppRadGood C R)
    {U : Type*} [Group U] [Finite U] (hU : CFSG.IsQuasisimple U)
    (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    (φ : U →* ↥C) (hφ : Function.Surjective φ) (hφ1 : ∃ u, φ u ≠ 1)
    {Q : Subgroup U} (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ⊤ Q) : GGOppRadGood ⊤ Q := by
  set ψ : U →* G := C.subtype.comp φ with hψ
  have hrange : ψ.range = C := by
    rw [hψ, MonoidHom.range_comp, (MonoidHom.range_eq_top).mpr hφ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hkerφ : φ.ker ≤ Subgroup.center U :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hU hφ1
  have hker : ψ.ker ≤ Subgroup.center U := fun z hz => hkerφ (by
    rw [MonoidHom.mem_ker] at hz ⊢
    exact Subtype.ext hz)
  have hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := fun z hz h2 => hZ z (hker hz) h2
  have hperf : commutator U = ⊤ := hU.1.commutator_eq_top
  refine GGOppRad.GGOppRadGood.of_map_perfect ψ hperf hker hinv hQ ?_
  have hrad := GGOppRad.radicalTwo_map ψ hker hinv hQ
  rw [hrange] at hrad ⊢
  refine hC _ ?_ hrad
  intro hbot
  apply hQne
  have hc := GGOppRad.card_map_eq ψ hinv hQ.isPGroup
  rw [hbot, Subgroup.card_bot] at hc
  exact Subgroup.eq_bot_of_card_eq Q hc.symm

theorem image_orbitUnion_of_longest_E6 {w₀ : WeylGroup TwistTag.E6.tag}
    {δ : Fin TwistTag.E6.tag.rank → Fin TwistTag.E6.tag.rank}
    (hmax : ∀ w, (coxeterSystem TwistTag.E6.tag).length w ≤
      (coxeterSystem TwistTag.E6.tag).length w₀)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    δ '' TwistTag.E6.orbitUnion J = TwistTag.E6.orbitUnion J := by
  have hrev : ReversesSigns CFSG.RankThree.Chevalley.e6HRReflProd := fun α _ hα => by
    rw [CFSG.RankThree.Chevalley.e6HRReflProd_smul, height_neg, height_permLattice]
    omega
  have hw : w₀ = CFSG.RankThree.Chevalley.e6HRReflProd :=
    (reversesSigns_of_forall_length_le hmax).eq hrev
  have hδρ : ∀ i, δ i = TwistTag.E6.perm i := fun i => by
    have h := hδ i
    rw [hw, CFSG.RankThree.Chevalley.e6HRReflProd_smul, permLattice_single] at h
    exact (single_injective_one (neg_injective h)).symm
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hδρ]
    exact perm_mem_orbitUnion hi
  · intro hj
    exact ⟨TwistTag.E6.perm.symm j, perm_symm_mem_orbitUnion hj, by
      rw [hδρ, Equiv.apply_symm_apply]⟩

theorem image_orbitUnion_of_longest_D4 {w₀ : WeylGroup TwistTag.D4.tag}
    {δ : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank}
    (hmax : ∀ w, (coxeterSystem TwistTag.D4.tag).length w ≤
      (coxeterSystem TwistTag.D4.tag).length w₀)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    δ '' TwistTag.D4.orbitUnion J = TwistTag.D4.orbitUnion J := by
  have hrev : ReversesSigns CFSG.RankThree.PartOne.Q1327T.d4NegOne := fun α _ hα => by
    rw [CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul, height_neg]
    omega
  have hw : w₀ = CFSG.RankThree.PartOne.Q1327T.d4NegOne :=
    (reversesSigns_of_forall_length_le hmax).eq hrev
  have hδid : ∀ i, δ i = i := fun i => by
    have h := hδ i
    rw [hw, CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single] at h
    exact (single_injective_one (neg_injective h)).symm
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    rwa [hδid i]
  · intro hj
    exact ⟨j, hj, hδid j⟩

theorem image_orbitUnion_of_longest (t : TwistTag) {w₀ : WeylGroup t.tag}
    {δ : Fin t.tag.rank → Fin t.tag.rank}
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin t.foldedTag.rank)) : δ '' t.orbitUnion J = t.orbitUnion J := by
  cases t with
  | E6 => exact image_orbitUnion_of_longest_E6 (w₀ := w₀) (δ := δ) hmax hδ J
  | D4 => exact image_orbitUnion_of_longest_D4 (w₀ := w₀) (δ := δ) hmax hδ J

theorem hasGoodOppositePRadicals_graphFixedRootGroup
    (t : TwistTag) {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r]
    (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom)]
    {Q : Subgroup (ModGL t.tag K)} (hQ : Q ≠ ⊥)
    (hQrad : CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom) Q) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r (graphFixedRootGroup t K σ.toRingHom) Q := by
  obtain ⟨w₀, δ, hmax, hδδ, hδ, -⟩ := exists_longest_fixed_data t
  exact hasGoodOppositePRadicals_graphFixedRootGroup_of_longest (t := t) (w₀ := w₀) (δ := δ)
    r σ hσ hmax hδδ hδ (image_orbitUnion_of_longest t hmax hδ) hQ hQrad

theorem hasGoodOppositePRadicals_top_graphFixedRootGroup
    (t : TwistTag) {K : Type} [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r]
    (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom)]
    {Q : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)}
    (hQ : Q ≠ ⊥) (hQrad : CFSG.GroupTheory.IsRadicalPGroup r ⊤ Q) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r ⊤ Q := by
  have hQ' : Q.map (graphFixedRootGroup t K σ.toRingHom).subtype ≠ ⊥ := by
    intro hbot
    apply hQ
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Q)
      (f := (graphFixedRootGroup t K σ.toRingHom).subtype)
      (Subgroup.subtype_injective _)).mp hbot
  have hQrad' : CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom)
      (Q.map (graphFixedRootGroup t K σ.toRingHom).subtype) :=
    (CFSG.GroupTheory.isRadicalPGroup_top_map_subtype_iff
      (C := graphFixedRootGroup t K σ.toRingHom) r Q).mp hQrad
  exact CFSG.GroupTheory.hasGoodOppositePRadicals_top_of_map_subtype
    (C := graphFixedRootGroup t K σ.toRingHom)
    (hasGoodOppositePRadicals_graphFixedRootGroup t σ hσ hQ' hQrad')

theorem ggOppRadGood_twistedE6RootGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)]
    {R : Subgroup (ModGL TwistTag.E6.tag K)} (hR : R ≠ ⊥)
    (hRad : GGRadicalTwo (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) R) :
    GGOppRadGood (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) R := by
  obtain ⟨w₀, δ, hmax, hδδ, hδ, -⟩ := exists_longest_fixed_data TwistTag.E6
  exact ggOppRadGood_graphFixedRootGroup σ hσ hmax hδδ hδ
    (image_orbitUnion_of_longest_E6 hmax hδ) hR hRad

end GGOppRadExc

section Tags

theorem ggOppositeRadicalUniversalAt_twistedE6 : GGOppositeRadicalUniversalAt .twistedE6 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  change Finite (twistedE6Group 2 f) ∧
    (∀ z ∈ Subgroup.center (twistedE6Group 2 f), z ^ 2 = 1 → z = 1) ∧
    ∀ Q : Subgroup (twistedE6Group 2 f), Q ≠ ⊥ → GGRadicalTwo ⊤ Q → GGOppRadGood ⊤ Q
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  set σ := iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f with hσdef
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have : Finite (twistedE6Group 2 f) := by
    have : Finite (Module.End (GaloisField 2 (2 * f))
        (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ GaloisField 2 (2 * f))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    infer_instance
  have := finite_modGL (τ := TwistTag.E6.tag) (K := GaloisField 2 (2 * f))
  have hU := CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hf
  have hZ : ∀ z ∈ Subgroup.center (twistedE6Group 2 f), z ^ 2 = 1 → z = 1 :=
    CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_fixedGroup (p := 2) (frobQ 2 f)
      (frobQ_frobQ 2 f hf)
  have hπ1 : ∃ u, π u ≠ 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, hQP, -, -, -, -, -, -, -, -, hne⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 (GaloisField 2 (2 * f)) σ ∅
    have : Nonempty (Fin TwistTag.E6.foldedTag.rank) := ⟨⟨0, by decide⟩⟩
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left (hne Set.empty_ne_univ)
    obtain ⟨u, hu⟩ := hπ ⟨x, (hQP.trans (graphFixedParabolic_le _ _ _ ∅)) hx⟩
    refine ⟨u, fun h => hx1 ?_⟩
    rw [h] at hu
    exact (congrArg Subtype.val hu).symm
  have hC₀ : IsSimpleGroup
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) σ.toRingHom) :=
    GGOppRadExc.isSimpleGroup_of_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hU hπ hπ1)
      (center_graphFixedRootGroup_eq_bot σ.surjective)
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    show σ ^ 2 = 1
    refine RingEquiv.ext fun c => ?_
    have h1 : ∀ x, σ x = frobQ 2 f x := fun x => RingHom.congr_fun hσθ x
    rw [pow_two]
    change σ (σ c) = c
    rw [h1, h1, frobQ_frobQ 2 f hf]
  refine ⟨inferInstance, hZ, fun Q hQne hQ => ?_⟩
  exact GGOppRadExc.ggOppRadGood_of_surjective_subgroup
    (fun R hR hRad => GGOppRadExc.ggOppRadGood_twistedE6RootGroup σ hσ2 hR hRad)
    hU hZ π hπ hπ1 hQne hQ

theorem ggOppositeRadicalCountNormalAt_twistedE6 : GGOppositeRadicalCountNormalAt .twistedE6 :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_twistedE6

theorem ggTwoSignalizerGenInput_holds : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_exceptional ggOppositeRadicalCountNormalAt_F4
    ggOppositeRadicalCountNormalAt_E6 ggOppositeRadicalCountNormalAt_E7
    ggOppositeRadicalCountNormalAt_E8 ggOppositeRadicalCountNormalAt_twistedE6

end Tags

end CFSG.StandardType
