module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

namespace HalfRowData

theorem center_eq_bot_of_pomegaMinus_two {Y : Type} [Group Y] [Group.IsPerfect Y]
    {n f : ℕ} (hL : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus n 2 f) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨-, hf, hn⟩ := hL.1
  have hodd : Odd ((2 ^ f) ^ n + 1) := by
    have hev2 : Even (2 ^ f) := by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    exact ((Nat.even_pow' (m := 2 ^ f) (n := n) (by omega)).mpr hev2).add_one
  have hcop : Nat.Coprime 4 ((2 ^ f) ^ n + 1) := by
    have h2 : Nat.Coprime 2 ((2 ^ f) ^ n + 1) := Nat.coprime_two_left.mpr hodd
    rw [show (4 : ℕ) = 2 * 2 by norm_num]
    exact Nat.Coprime.mul_left h2 h2
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus n 2 f = (1, 1) := by
    rw [show CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus n 2 f =
      (Nat.gcd 4 ((2 ^ f) ^ n + 1), 1) from rfl, Nat.coprime_iff_gcd_eq_one.mp hcop]
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus n 2 f = (1, 1) := rfl
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row hL
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y)) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    have h1 : Nat.card (Multiplicative (ZMod 1)) = 1 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hgen,
      hexc, Nat.card_prod, h1, mul_one]
  have hdvd :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl (Y ⧸ Subgroup.center Y))
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

end HalfRowData

private theorem eq_twD_of_ggLabelIso {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twD, 4, 1⟩) : lab = ⟨.twD, 4, 1⟩ := by
  obtain ⟨t, l, n⟩ := lab
  unfold GGLabelIso at h
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false, false_or]
    at h ⊢
  rcases h with h | h | h
  · exact h
  · simp_all
  · simp_all

private theorem eq_E6_of_ggLabelIso {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.E6, 0, 1⟩) : lab = ⟨.E6, 0, 1⟩ := by
  obtain ⟨t, l, n⟩ := lab
  unfold GGLabelIso at h
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false, false_or]
    at h ⊢
  exact h

private theorem subsingleton_units_of_card_eq_two {K : Type} [Field K]
    (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h1 : Nat.card Kˣ = 1 := by
    simp [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.mp h1).1

private theorem exists_inner_of_induces {G : Type} [Group G] {K' : Subgroup G} {R : Type}
    [Group R] (hZ : Subgroup.center ↥K' = ⊥) (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K' : Set G)) {r : R}
    (hb : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (MulAut.conj r)) :
    ∃ c ∈ K', ∀ l ∈ K', b * l * b⁻¹ = c * l * c⁻¹ := by
  obtain ⟨x, hx⟩ := θ.surjective r
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨(c₀⁻¹ : ↥K'), (c₀⁻¹).2, ?_⟩
  intro l hl
  have hl₁ : b * l * b⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp hbN l).mp hl
  have hrel : l = b⁻¹ * (b * l * b⁻¹) * b := by group
  have hkey := hb ⟨b * l * b⁻¹, hl₁⟩ ⟨l, hl⟩ hrel
  have hkey' : θ (QuotientGroup.mk (c₀ * (⟨b * l * b⁻¹, hl₁⟩ : ↥K') * c₀⁻¹)) =
      θ (QuotientGroup.mk (⟨l, hl⟩ : ↥K')) := by
    have h := hkey
    rw [← hx, MulAut.conj_apply] at h
    simp only [← QuotientGroup.mk'_apply] at h ⊢
    simp only [map_mul, map_inv] at h ⊢
    exact h
  have hmk : QuotientGroup.mk (c₀ * (⟨b * l * b⁻¹, hl₁⟩ : ↥K') * c₀⁻¹) =
      QuotientGroup.mk (⟨l, hl⟩ : ↥K') := θ.injective hkey'
  have hmem : (c₀ * (⟨b * l * b⁻¹, hl₁⟩ : ↥K') * c₀⁻¹)⁻¹ * (⟨l, hl⟩ : ↥K') ∈
      Subgroup.center ↥K' := QuotientGroup.eq.mp hmk
  rw [hZ, Subgroup.mem_bot] at hmem
  have hlm : (⟨l, hl⟩ : ↥K') = c₀ * (⟨b * l * b⁻¹, hl₁⟩ : ↥K') * c₀⁻¹ :=
    (inv_mul_eq_one.mp hmem).symm
  have hG : l = (c₀ : G) * (b * l * b⁻¹) * (c₀ : G)⁻¹ := by
    have := congrArg (fun x : ↥K' => (x : G)) hlm
    simpa using this
  have hc : ((c₀⁻¹ : ↥K') : G) * l * (((c₀⁻¹ : ↥K') : G))⁻¹ = b * l * b⁻¹ := by
    simp only [Subgroup.coe_inv, inv_inv]
    conv_lhs => rw [hG]
    group
  exact hc.symm

theorem ggHalfRowDataInput_holds :
    GGHalfRowDataInput := by
  intro G _ _ Bs K' hInn hlab
  obtain ⟨hperf, lab, hlabΛ, hraw⟩ := largeEvenMarking_markedModel hInn
  have hHas : GGHasLabel lab (↥K' ⧸ Subgroup.center ↥K') :=
    largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  rcases hlab with hlab | hlab
  ·
    have hlab' : lab = ⟨.twD, 4, 1⟩ :=
      eq_twD_of_ggLabelIso
        (ggLabelRigidInput_holds lab ⟨.twD, 4, 1⟩ (↥K' ⧸ Subgroup.center ↥K') hlabΛ
          (by unfold LargeEvenInLambda2; norm_num) hHas hlab)
    subst hlab'
    obtain ⟨K, hF, hfin, hK, bf, cf, hbc, hq⟩ := hraw
    letI : Field K := hF
    letI : Finite K := hfin
    obtain ⟨-, -, θ, hP, -⟩ := hq
    obtain ⟨hBN, hB⟩ := hP
    haveI : Group.IsPerfect ↥K' := ⟨hperf⟩
    have hZ : Subgroup.center ↥K' = ⊥ :=
      HalfRowData.center_eq_bot_of_pomegaMinus_two
        (statedClassicalModel_of_mulEquiv' θ.symm
          (statedClassicalModel_omegaMinus 4 1 hK bf cf hbc
            (⟨Nat.prime_two, le_rfl, le_rfl⟩ : StatedLieAdmissible .POmegaMinus 4 2 1)))
    refine ⟨hZ, ?_⟩
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hB b hb
    simp only [LargeEvenInnSet, Set.mem_range] at hφI
    obtain ⟨r, hr⟩ := hφI
    rw [← hr] at hφ
    exact exists_inner_of_induces hZ θ (hBN hb) hφ
  ·
    have hlab' : lab = ⟨.E6, 0, 1⟩ :=
      eq_E6_of_ggLabelIso
        (ggLabelRigidInput_holds lab ⟨.E6, 0, 1⟩ (↥K' ⧸ Subgroup.center ↥K') hlabΛ
          (by unfold LargeEvenInLambda2; norm_num) hHas hlab)
    subst hlab'
    obtain ⟨K, hF, hfin, hK, hq⟩ := hraw
    letI : Field K := hF
    letI : Finite K := hfin
    obtain ⟨-, -, θ, hP, hM⟩ := hq
    obtain ⟨hBN, hB⟩ := hP
    haveI : Group.IsPerfect ↥K' := ⟨hperf⟩
    have hZ : Subgroup.center ↥K' = ⊥ :=
      ggSixE6A24_center_eq_bot ↥K' hperf (MarkedModel.of_mulEquiv θ.symm hM)
    refine ⟨hZ, ?_⟩
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hB b hb
    have hK2 : Nat.card K = 2 := by simpa using hK
    haveI : Subsingleton Kˣ := subsingleton_units_of_card_eq_two hK2
    obtain ⟨r, hr⟩ :=
      chevIDImage_subset_inn_of_subsingleton
        (LargeEvenChevH (LargeEvenCartanE 6) K false) hφI
    rw [← hr] at hφ
    exact exists_inner_of_induces hZ θ (hBN hb) hφ

end CFSG.StandardType

end
