module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Def
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.Quasithin.Background.G11Stmts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.StandardType.D4Rank
open CFSG.SeitzReduction.OmegaPilot
open CFSG.Quasithin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal
open Matrix

open scoped Matrix

variable {K : Type} [Field K]

private theorem s16kOm8_reindex_symm_act
    (g : ↥(StatedOmega (StatedQuadPlus 4 K))) (v : Fin (2 * 4) → K) :
    (reindexVectorEquiv (plusIndexEquiv 4)).symm (act (statedDerivedPlusEquiv K 4 g) v) =
      (g : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ
        (reindexVectorEquiv (plusIndexEquiv 4)).symm v := by
  unfold statedDerivedPlusEquiv
  have hvec := statedDerivedReindexEquiv_vector (plusIndexEquiv 4)
    (CFSG.LieType.Universal.Spin.quadPlus 4 K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) g
    ((reindexVectorEquiv (plusIndexEquiv 4)).symm v)
  rw [LinearEquiv.apply_symm_apply] at hvec
  change (reindexVectorEquiv (plusIndexEquiv 4)).symm
      (matrixLinearEquiv (statedDerivedReindexEquiv (plusIndexEquiv 4)
        (CFSG.LieType.Universal.Spin.quadPlus 4 K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) g).val v) =
    (g : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ
      (reindexVectorEquiv (plusIndexEquiv 4)).symm v
  rw [hvec, LinearEquiv.symm_apply_apply, toLinEquiv_apply]

private theorem s16kOm8_act_reindex_symm
    (g : ↥(StatedOmega (StatedQuadPlus 4 K))) (w : Fin 4 ⊕ Fin 4 → K) :
    act (statedDerivedPlusEquiv K 4 g) (reindexVectorEquiv (plusIndexEquiv 4) w) =
      reindexVectorEquiv (plusIndexEquiv 4) ((g : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ w) := by
  let L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    (reindexVectorEquiv (plusIndexEquiv 4)).symm
  have hL : L.symm = reindexVectorEquiv (plusIndexEquiv 4) := LinearEquiv.symm_symm _
  rw [← hL, eq_comm, LinearEquiv.symm_apply_eq, s16kOm8_reindex_symm_act g (L.symm w),
    LinearEquiv.apply_symm_apply]

@[expose] def Om8TwistIso {K : Type} [Field K] (a b : MulAut (Om8 K)) : Prop :=
  ∃ T : (Fin (2 * 4) → K) ≃+ (Fin (2 * 4) → K), ∀ (x : Om8 K) (v : Fin (2 * 4) → K),
    T (act (a x) v) = act (b x) (T v)

private theorem s16kOm8_twistIso_transport [Finite K]
    (a b : MulAut ↥(StatedOmega (StatedQuadPlus 4 K)))
    (T : Multiplicative (Fin 4 ⊕ Fin 4 → K) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K))
    (hT : ∀ (x : ↥(StatedOmega (StatedQuadPlus 4 K)))
      (v : Multiplicative (Fin 4 ⊕ Fin 4 → K)),
      T (natAct (StatedOmega (StatedQuadPlus 4 K)) (a x) v) =
        natAct (StatedOmega (StatedQuadPlus 4 K)) (b x) (T v)) :
    Om8TwistIso (MulAut.congr (statedDerivedPlusEquiv K 4) a)
      (MulAut.congr (statedDerivedPlusEquiv K 4) b) := by
  let R : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    reindexVectorEquiv (plusIndexEquiv 4)
  let L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := R.symm
  let Ta : (Fin 4 ⊕ Fin 4 → K) ≃+ (Fin 4 ⊕ Fin 4 → K) :=
    (AddEquiv.toMultiplicative (G := Fin 4 ⊕ Fin 4 → K)
      (H := Fin 4 ⊕ Fin 4 → K)).symm T
  refine ⟨L.toAddEquiv.trans (Ta.trans R.toAddEquiv), fun y v => ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x, statedDerivedPlusEquiv K 4 x = y :=
    ⟨(statedDerivedPlusEquiv K 4).symm y, (statedDerivedPlusEquiv K 4).apply_symm_apply y⟩
  rw [show (MulAut.congr (statedDerivedPlusEquiv K 4) a) (statedDerivedPlusEquiv K 4 x) =
        statedDerivedPlusEquiv K 4 (a x) by
      change (statedDerivedPlusEquiv K 4) (a ((statedDerivedPlusEquiv K 4).symm
        ((statedDerivedPlusEquiv K 4) x))) = statedDerivedPlusEquiv K 4 (a x)
      rw [MulEquiv.symm_apply_apply],
    show (MulAut.congr (statedDerivedPlusEquiv K 4) b) (statedDerivedPlusEquiv K 4 x) =
        statedDerivedPlusEquiv K 4 (b x) by
      change (statedDerivedPlusEquiv K 4) (b ((statedDerivedPlusEquiv K 4).symm
        ((statedDerivedPlusEquiv K 4) x))) = statedDerivedPlusEquiv K 4 (b x)
      rw [MulEquiv.symm_apply_apply]]
  change R (Ta (L (act (statedDerivedPlusEquiv K 4 (a x)) v))) =
    act (statedDerivedPlusEquiv K 4 (b x)) (R (Ta (L v)))
  rw [s16kOm8_reindex_symm_act (a x) v]
  have hTa : Ta ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ L v) =
      (b x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ Ta (L v) := by
    change Multiplicative.toAdd (T (Multiplicative.ofAdd ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ
        L v))) =
      (b x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ
        Multiplicative.toAdd (T (Multiplicative.ofAdd (L v)))
    rw [show Multiplicative.ofAdd ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ L v) =
        natAct (StatedOmega (StatedQuadPlus 4 K)) (a x)
          (Multiplicative.ofAdd (L v)) from rfl,
      hT x (Multiplicative.ofAdd (L v))]
    rfl
  rw [hTa]
  rw [← s16kOm8_act_reindex_symm (b x) (Ta (L v))]

private theorem s16kOm8_twistIso_transport_symm [Finite K]
    (a b : MulAut ↥(StatedOmega (StatedQuadPlus 4 K)))
    (T' : (Fin (2 * 4) → K) ≃+ (Fin (2 * 4) → K))
    (hT' : ∀ (y : Om8 K) (v : Fin (2 * 4) → K),
      T' (act ((MulAut.congr (statedDerivedPlusEquiv K 4) a) y) v) =
        act ((MulAut.congr (statedDerivedPlusEquiv K 4) b) y) (T' v)) :
    S16kTwistIso a b := by
  let R : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    reindexVectorEquiv (plusIndexEquiv 4)
  let L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := R.symm
  let Ta : (Fin 4 ⊕ Fin 4 → K) ≃+ (Fin 4 ⊕ Fin 4 → K) :=
    R.toAddEquiv.trans (T'.trans L.toAddEquiv)
  refine ⟨AddEquiv.toMultiplicative Ta, fun x v => ?_⟩
  change Ta ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ Multiplicative.toAdd v) =
    (b x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ Ta (Multiplicative.toAdd v)
  have hx : (MulAut.congr (statedDerivedPlusEquiv K 4) a) (statedDerivedPlusEquiv K 4 x) =
      statedDerivedPlusEquiv K 4 (a x) := by
    change (statedDerivedPlusEquiv K 4) (a ((statedDerivedPlusEquiv K 4).symm
      ((statedDerivedPlusEquiv K 4) x))) = statedDerivedPlusEquiv K 4 (a x)
    rw [MulEquiv.symm_apply_apply]
  have hx' : (MulAut.congr (statedDerivedPlusEquiv K 4) b) (statedDerivedPlusEquiv K 4 x) =
      statedDerivedPlusEquiv K 4 (b x) := by
    change (statedDerivedPlusEquiv K 4) (b ((statedDerivedPlusEquiv K 4).symm
      ((statedDerivedPlusEquiv K 4) x))) = statedDerivedPlusEquiv K 4 (b x)
    rw [MulEquiv.symm_apply_apply]
  have h1 : Ta ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ Multiplicative.toAdd v) =
      L (T' (act (statedDerivedPlusEquiv K 4 (a x)) (R (Multiplicative.toAdd v)))) := by
    change L (T' (R ((a x : GL (Fin 4 ⊕ Fin 4) K).val *ᵥ Multiplicative.toAdd v))) = _
    rw [s16kOm8_act_reindex_symm (a x) (Multiplicative.toAdd v)]
  rw [h1, ← hx, hT' (statedDerivedPlusEquiv K 4 x) (R (Multiplicative.toAdd v)), hx']
  rw [s16kOm8_reindex_symm_act (b x) (T' (R (Multiplicative.toAdd v)))]
  rfl

theorem s16kTwistIso_iff_om8 {K : Type} [Field K] [Finite K]
    (a b : MulAut ↥(StatedOmega (StatedQuadPlus 4 K))) :
    S16kTwistIso a b ↔
      Om8TwistIso (MulAut.congr (statedDerivedPlusEquiv K 4) a)
        (MulAut.congr (statedDerivedPlusEquiv K 4) b) := by
  constructor
  · rintro ⟨T, hT⟩
    exact s16kOm8_twistIso_transport a b T hT
  · rintro ⟨T', hT'⟩
    exact s16kOm8_twistIso_transport_symm a b T' hT'

private theorem s16kOm8_statedScalars_eq_bot (hK : Nat.card K = 2) :
    StatedScalars (Fin 4 ⊕ Fin 4) K = ⊥ := by
  have hunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units K, hK]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  rw [StatedScalars, MonoidHom.range_eq_bot_iff]
  ext c
  rw [Subsingleton.elim c 1]
  simp

private theorem s16kOm8_statedScalars_subgroupOf_eq_bot (hK : Nat.card K = 2) :
    (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) = ⊥ := by
  rw [s16kOm8_statedScalars_eq_bot hK, Subgroup.bot_subgroupOf]

private noncomputable def s16kOm8_statedProj_equiv (hK : Nat.card K = 2) :
    ↥(StatedOmega (StatedQuadPlus 4 K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (QuotientGroup.quotientBot).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (s16kOm8_statedScalars_subgroupOf_eq_bot hK).symm)

theorem lieModel_om8 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CFSG.Blueprint.LieModel (Om8 K) .POmegaPlus 4 2 1 := by
  refine Or.inl ⟨by decide, ?_⟩
  unfold StatedClassicalModel
  exact ⟨⟨by decide, le_refl _, le_refl _⟩, K, inferInstance, inferInstance, by simpa using hK,
    ⟨(statedDerivedPlusEquiv K 4).symm.trans (s16kOm8_statedProj_equiv hK)⟩⟩

private theorem s16kOm8_statedClassicalModel {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    StatedClassicalModel (Om8 K) .POmegaPlus 4 2 1 := by
  rcases lieModel_om8 hK with ⟨-, h⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact h
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem om8_center_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Subgroup.center (Om8 K) = ⊥ := by
  haveI hsimple : IsSimpleGroup (Om8 K) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
      (Om8 K) 4 2 1 (s16kOm8_statedClassicalModel hK)).2
  refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
  intro hcomm
  haveI : IsMulCommutative (Om8 K) := hcomm
  have hcard : Nat.card (Om8 K) = 174182400 := by
    have := (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaPlus) (n := 4) (f := 1)
      (s16kOm8_statedClassicalModel hK)).2.2.2.1 rfl
    rw [this]
    decide
  have hp : (Nat.card (Om8 K)).Prime := (Group.is_simple_iff_prime_card).mp hsimple
  rw [hcard] at hp
  exact absurd hp (by norm_num)

theorem om8_card_mulAut {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card (MulAut (Om8 K)) = 6 * Nat.card (Om8 K) := by
  rw [CFSG.EvenSmallLie.OmegaEight.card_mulAut_of_lieModel (lieModel_om8 hK),
    CFSG.EvenSmallLie.OmegaEight.card_of_lieModel (lieModel_om8 hK)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
