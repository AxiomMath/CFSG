module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullFull
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FixedPointModel

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian 2 E) (L : Subgroup G) :
    IsElemAbelian 2 (E.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hE L

theorem isElemAbelian_of_le {E Q : Subgroup G} (hQ : IsElemAbelian 2 Q) (hEQ : E ≤ Q) :
    IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hQ hEQ

theorem two_le_twoRank_of_le [Finite G] {E L : Subgroup G} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (hEL : E ≤ L) : 2 ≤ twoRank L := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun x =>
    ⟨1, by simpa only [pow_one] using Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcard : Nat.card (E.subgroupOf L) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hk]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk2.trans (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary L _
    (isElemAbelian_subgroupOf hE L) k hcard)

theorem orbit_coset_embedding (H L : Subgroup G) :
    ∃ ι : L ⧸ H.subgroupOf L → rightCosetSpace H, Function.Injective ι ∧
      Set.range ι = {omega | ∃ l ∈ L, rightCosetTranslate H (rightCosetMk H 1) l = omega} ∧
      ι (QuotientGroup.mk 1) = rightCosetMk H 1 ∧
      ∀ (l : L) (x : L ⧸ H.subgroupOf L), ι (l • x) = rightCosetTranslate H (ι x) (l : G)⁻¹ := by
  let : MulAction L (rightCosetSpace H) :=
    { smul := fun l omega => rightCosetTranslate H omega (l : G)⁻¹
      one_smul := fun omega => by
        change rightCosetTranslate H omega ((1 : L) : G)⁻¹ = omega
        rw [Subgroup.coe_one, inv_one, rightCosetTranslate_one]
      mul_smul := fun l k omega => by
        change rightCosetTranslate H omega ((l * k : L) : G)⁻¹ =
          rightCosetTranslate H (rightCosetTranslate H omega (k : G)⁻¹) (l : G)⁻¹
        rw [rightCosetTranslate_mul, Subgroup.coe_mul, mul_inv_rev] }
  let α := rightCosetMk H 1
  have hsmul : ∀ (l : L) (omega : rightCosetSpace H),
      l • omega = rightCosetTranslate H omega (l : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer L α = H.subgroupOf L := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, translate_base_iff, Subgroup.mem_subgroupOf,
      H.inv_mem_iff]
  let ι : L ⧸ H.subgroupOf L → rightCosetSpace H :=
    MulAction.ofQuotientStabilizer L α ∘ Subgroup.quotientEquivOfEq hstab.symm
  have hι : ∀ l : L, ι (QuotientGroup.mk l) = rightCosetTranslate H α (l : G)⁻¹ := by
    intro l
    change MulAction.ofQuotientStabilizer L α
      (Subgroup.quotientEquivOfEq hstab.symm (QuotientGroup.mk l)) = _
    rw [Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk, hsmul]
  refine ⟨ι, (MulAction.injective_ofQuotientStabilizer L α).comp
    (Subgroup.quotientEquivOfEq hstab.symm).injective, ?_, ?_, ?_⟩
  · ext omega
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H l => exact ⟨(l : G)⁻¹, L.inv_mem l.2, (hι l).symm⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨QuotientGroup.mk (⟨g, hg⟩ : L)⁻¹, ?_⟩
      rw [hι, Subgroup.coe_inv, inv_inv]
  · rw [hι, Subgroup.coe_one, inv_one, rightCosetTranslate_one]
  · intro l x
    induction x using QuotientGroup.induction_on with
    | H k =>
      change ι (QuotientGroup.mk (l * k)) = _
      rw [hι, hι, rightCosetTranslate_mul, Subgroup.coe_mul, mul_inv_rev]

theorem base_orbit_eq_hull_orbit {H Y : Subgroup G} {r : G}
    (h : InvolutionPointLocalEmbedding H r) (hrY : r ∈ Y)
    (hclass : conjugacyWithin Y r = conjugacyWithin (Subgroup.closure (conjugacyWithin Y r)) r) :
    {omega : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | ∃ l ∈ Subgroup.closure (conjugacyWithin Y r),
        rightCosetTranslate H (rightCosetMk H 1) l = omega} := by
  let L := Subgroup.closure (conjugacyWithin Y r)
  have hLY : L ≤ Y := properHull_le Y hrY
  ext omega
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hmem : (y : G)⁻¹ * r * y ∈ conjugacyWithin L r := by
      rw [← hclass]
      exact ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨l, hl⟩ := hmem
    have hc : y * (l : G)⁻¹ ∈ Subgroup.centralizer ({r} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h' : (l : G) * y⁻¹ * r * y * (l : G)⁻¹ = r := by
        rw [show (l : G) * y⁻¹ * r * y * (l : G)⁻¹ = (l : G) * (y⁻¹ * r * y) * (l : G)⁻¹ by
          group, ← hl]
        group
      calc y * (l : G)⁻¹ * r = y * (l : G)⁻¹ * ((l : G) * y⁻¹ * r * y * (l : G)⁻¹) := by
            rw [h']
        _ = r * (y * (l : G)⁻¹) := by group
    refine ⟨l, l.2, ?_⟩
    have hcH : y * (l : G)⁻¹ ∈ H := point_centralizer_le h hc
    rw [show y = (y * (l : G)⁻¹) * l by group, ← rightCosetTranslate_mul,
      (translate_base_iff H _).mpr hcH]
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hLY hl, rfl⟩

variable [Finite G]

theorem class_hull_rank_two {H Y : Subgroup G} {r : G}
    (h : MinimalInvolutionPointLocalFailure H r)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (hY : Y < ⊤) (hrY : r ∈ Y) (hYH : ¬ Y ≤ H) {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (hEL : E ≤ Subgroup.closure (conjugacyWithin Y r)) :
    let L := Subgroup.closure (conjugacyWithin Y r)
    let R := (CFSG.oddCore Y).map Y.subtype
    2 ≤ twoRank L ∧ fusionStronglyEmbedded (H.subgroupOf L) ∧
      conjugacyWithin Y r = conjugacyWithin L r ∧ ⁅R, L⁆ = ⊥ ∧ R ≤ H ∧
      (CFSG.oddCore L).map L.subtype ≤ R ∧ CFSG.oddCore L ≤ Subgroup.center L ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧ R1Full L ∧ fusionIsBenderGroup (L ⧸ CFSG.oddCore L) ∧
      {omega : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = omega} =
        {omega : rightCosetSpace H | ∃ l ∈ L,
          rightCosetTranslate H (rightCosetMk H 1) l = omega} := by
  intro L R
  have hrank : 2 ≤ twoRank L := two_le_twoRank_of_le hE hE4 hEL
  obtain ⟨hstrong, hclass, hxor⟩ :=
    minimalLocalFailure_proper_local_hull_dichotomy h hcomm hsmallerR1 hY hrY hYH
  obtain ⟨-, hRL, hR1, -, hmodel, -⟩ : 2 ≤ twoRank L ∧ ⁅R, L⁆ = ⊥ ∧ R1Full L ∧
      (∃ _ : (⊤ : Subgroup L).Normal, CFSG.oddCore L < ⊤ ∧ Odd (⊤ : Subgroup L).index ∧
        fusionIsBenderGroup ((⊤ : Subgroup L) ⧸ (CFSG.oddCore L).subgroupOf ⊤)) ∧
      fusionIsBenderGroup (L ⧸ CFSG.oddCore L) ∧ ExplicitRankOneModel (L ⧸ CFSG.oddCore L) := by
    rcases hxor with ⟨hone, -⟩ | ⟨htwo, -⟩
    · have h1 : twoRank L = 1 := hone.1
      omega
    · exact htwo
  have hLY : L ≤ Y := properHull_le Y hrY
  have hrL : r ∈ L := distinguished_mem_properHull Y r
  have hRcent : R ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRL
  have hRH : R ≤ H := fun x hx =>
    point_centralizer_le h.local_datum (Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hRcent hx)) r hrL).symm)
  have : (L.subgroupOf Y).Normal := properHull_normal_in_subgroup Y hrY
  have hRLR : (CFSG.oddCore L).map L.subtype ≤ R := by
    rintro x ⟨x', hx', rfl⟩
    exact ⟨Subgroup.inclusion hLY x',
      (CFSG.ComponentClassification.OddCore.normal_step_mem_iff hLY x').mp hx', rfl⟩
  have hcore : ∀ x ∈ CFSG.oddCore L, (x : G) ∈ R := fun x hx =>
    hRLR (Subgroup.mem_map_of_mem L.subtype hx)
  refine ⟨hrank, hstrong, hclass, hRL, hRH, hRLR, fun x hx => ?_, fun x hx => hRH (hcore x hx),
    hR1, hmodel, base_orbit_eq_hull_orbit h.local_datum hrY hclass⟩
  refine Subgroup.mem_center_iff.mpr fun l => Subtype.ext ?_
  exact (Subgroup.mem_centralizer_iff.mp (hRcent (hcore x hx))) l l.2

end CFSG.ShultStronglyClosedTI.FixedPointModel
