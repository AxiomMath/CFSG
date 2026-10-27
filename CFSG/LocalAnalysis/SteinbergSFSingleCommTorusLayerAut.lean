module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommTorusLayerCore
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace TorusLayer

open Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.RankThree.PartOne.KCRootAxis
  CFSG.ComponentClassification.OuterAutomorphisms

section Aut

variable {X : Type*} [Group X] {K : Type} [Field K]

theorem exists_fixed_root_action [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {Sb : Subgroup X} (e' : SL₂ K ≃* ↥Sb) {a : X}
    (hle : Sb ≤ centralizer ({a} : Set X))
    (hnorm : (Sb.subgroupOf (centralizer ({a} : Set X))).Normal)
    (hCC : centralizer (Sb : Set X) ⊓ centralizer ({a} : Set X) = zpowers a) :
    ∃ ρ : ↥(centralizer ({a} : Set X)) →* MulAut (SL₂ K),
      (∀ c Y, (e' (ρ c Y) : X) = (c : X) * e' Y * (c : X)⁻¹) ∧
      ρ.ker = (zpowers a).subgroupOf (centralizer ({a} : Set X)) ∧
      inner (SL₂ K) ≤ ρ.range ∧
      (∃ ι : ↥ρ.range ⧸ (inner (SL₂ K)).subgroupOf ρ.range →* (K ≃+* K),
        Function.Injective ι) ∧
      IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = n := by
  set C := centralizer ({a} : Set X)
  let E : ↥(Sb.subgroupOf C) ≃* SL₂ K := (subgroupOfEquivOfLe hle).trans e'.symm
  let ρ : ↥C →* MulAut (SL₂ K) := (MulAut.congr E).toMonoidHom.comp MulAut.conjNormal
  have hρ : ∀ c Y, (e' (ρ c Y) : X) = (c : X) * e' Y * (c : X)⁻¹ := by
    intro c Y
    change (e' (e'.symm (subgroupOfEquivOfLe hle (MulAut.conjNormal c (E.symm Y)))) : X) = _
    rw [MulEquiv.apply_symm_apply]
    change ((MulAut.conjNormal c (E.symm Y) : ↥C) : X) = _
    rw [MulAut.conjNormal_apply]
    rfl
  have hker : ρ.ker = (zpowers a).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hCC]
    constructor
    · intro hc
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, c.2⟩
      obtain ⟨Y, hY⟩ := e'.surjective ⟨s, hs⟩
      have h1 := hρ c Y
      rw [hc, MulAut.one_apply, hY] at h1
      change s = (c : X) * s * (c : X)⁻¹ at h1
      calc s * c = (c : X) * s * (c : X)⁻¹ * c := by rw [← h1]
        _ = c * s := by group
    · intro hc
      refine MulEquiv.ext fun Y => e'.injective (Subtype.ext ?_)
      rw [hρ, MulAut.one_apply]
      have h1 := mem_centralizer_iff.mp (mem_inf.mp hc).1 (e' Y) (e' Y).2
      calc (c : X) * e' Y * (c : X)⁻¹ = e' Y * c * (c : X)⁻¹ := by rw [← h1]
        _ = e' Y := by group
  have hinner : inner (SL₂ K) ≤ ρ.range := by
    rintro _ ⟨M, rfl⟩
    refine ⟨⟨e' M, hle (e' M).2⟩, MulEquiv.ext fun Y => e'.injective (Subtype.ext ?_)⟩
    rw [hρ]
    change (e' M : X) * e' Y * (e' M : X)⁻¹ = (e' (M * Y * M⁻¹) : X)
    rw [map_mul, map_mul, map_inv]
    rfl
  let ι' : ↥ρ.range →* Outer (SL₂ K) := (QuotientGroup.mk' (inner (SL₂ K))).comp ρ.range.subtype
  have hι' : (inner (SL₂ K)).subgroupOf ρ.range = ι'.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).symm
  have hcard : Nat.card (K ≃+* K) = n := by
    rw [Nat.card_congr (outFieldEquiv K).toEquiv, natCard_out_sl2 hn hK]
  refine ⟨ρ, hρ, hker, hinner, ⟨(outFieldEquiv K).symm.toMonoidHom.comp
    ((QuotientGroup.kerLift ι').comp (QuotientGroup.quotientMulEquivOfEq hι').toMonoidHom), ?_⟩,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K, hcard⟩
  exact (outFieldEquiv K).symm.injective.comp
    ((QuotientGroup.kerLift_injective ι').comp (QuotientGroup.quotientMulEquivOfEq hι').injective)

end Aut

@[expose] def TorusLayerConclusion (F : Type) [Group F] [Finite F] (K : Type) [Field K]
    (n : ℕ) (S J Y V : Subgroup F) (t : F) (hk : SL₂ K → F) : Prop :=
  let R := CFSG.Open.standardComponentOddCore F
  let θ : F →* F ⧸ R := QuotientGroup.mk' R
  let Sb := S.map θ
  let D := normalClosure (Sb : Set (F ⧸ R))
  let a := θ t
  CFSG.SectionRank.IsKGroupCat (F ⧸ R) ∧
  J ≤ R ∧ R ⊓ centralizer ({t} : Set F) = J ∧ ⁅R, Y⁆ = ⊥ ∧ centralizer (Y : Set F) = R ∧
  (center Y).map Y.subtype = (CFSG.Open.standardComponentOddCore Y).map Y.subtype ∧
  (CFSG.Open.standardComponentOddCore Y).map Y.subtype = Y ⊓ R ∧
  Set.InjOn θ (S : Set F) ∧ (∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F)) ∧
  orderOf a = 2 ∧ IsSimpleGroup Sb ∧ (∃ e : SL₂ K ≃* ↥Sb, ∀ X, (e X : F ⧸ R) = θ (hk X)) ∧
  centralizer ({a} : Set (F ⧸ R)) = (centralizer ({t} : Set F)).map θ ∧
  Sb ≤ centralizer ({a} : Set (F ⧸ R)) ∧
  (Sb.subgroupOf (centralizer ({a} : Set (F ⧸ R)))).Normal ∧
  centralizer (Sb : Set (F ⧸ R)) ⊓ centralizer ({a} : Set (F ⧸ R)) = zpowers a ∧
  CFSG.Open.standardComponentIsStandard Sb ∧ ¬ Sb.Normal ∧
  (∃ P : Sylow 2 ↥(centralizer (Sb : Set (F ⧸ R))),
    (P : Subgroup _).map (centralizer (Sb : Set (F ⧸ R))).subtype = zpowers a) ∧
  CFSG.Open.standardComponentOddCore (F ⧸ R) = ⊥ ∧ CFSG.pCore 2 (F ⧸ R) = ⊥ ∧
  CFSG.fittingSubgroup (F ⧸ R) = ⊥ ∧ D = CFSG.layer (F ⧸ R) ∧
  centralizer (D : Set (F ⧸ R)) = ⊥ ∧ Y.map θ = D ∧
  (∃ e : ↥Y ⧸ center ↥Y ≃* ↥D, ∀ y : Y, (e (y : ↥Y ⧸ center ↥Y) : F ⧸ R) = θ y) ∧
  CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayerAlternatives Sb D a ∧
  (IsSimpleGroup D → CFSG.Blueprint.Catalog D) ∧
  ((2 ^ n) ^ 2 < Nat.card V → IsSimpleGroup D ∧ CFSG.Blueprint.Catalog D) ∧
  ∃ ρ : ↥(centralizer ({a} : Set (F ⧸ R))) →* MulAut (SL₂ K),
    (∀ c X, θ (hk (ρ c X)) = (c : F ⧸ R) * θ (hk X) * (c : F ⧸ R)⁻¹) ∧
    ρ.ker = (zpowers a).subgroupOf (centralizer ({a} : Set (F ⧸ R))) ∧
    inner (SL₂ K) ≤ ρ.range ∧
    (∃ ι : ↥ρ.range ⧸ (inner (SL₂ K)).subgroupOf ρ.range →* (K ≃+* K),
      Function.Injective ι) ∧
    IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = n

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  {S : Subgroup F} {e : SL₂ K ≃* ↥S} {J V : Subgroup F} {t u w : F}

theorem torusLayerConclusion (h : LayerHyp n e J V t u w) {Y : Subgroup F}
    (hY : Y = normalClosure (S : Set F)) {hk : SL₂ K → F} (hke : ∀ X, hk X = e X) :
    TorusLayerConclusion F K n S J Y V t hk := by
  subst hY
  unfold TorusLayerConclusion
  intro R θ Sb D a
  obtain ⟨hinj, hinj2, hθt, hsimp, -, hle, hn, hCt, hCC, hstd, hsyl⟩ := quotient_facts h
  obtain ⟨hO2, hFit, -, hDE, hCD, halt, -⟩ := layer_conclusion h
  obtain ⟨e', he'⟩ := exists_equiv_map h
  obtain ⟨ρ, hρ, hρker, hρinn, hι, hcyc, hcard⟩ :=
    exists_fixed_root_action (by have := h.two_le; omega) h.card_K e' hle hn hCC
  have hKbar : CFSG.SectionRank.IsKGroupCat (F ⧸ R) := h.kgroup.quotient _
  have hcat : IsSimpleGroup D → CFSG.Blueprint.Catalog D := fun hs =>
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKbar D (MonoidHom.id _)
      Function.surjective_id
  refine ⟨hKbar, le_oddCore h.J_le h.J_odd, oddCore_inf_centralizer h,
    commutator_eq_bot_iff_le_centralizer.mpr (oddCore_le_centralizer h),
    centralizer_normalClosure h, (center_normalClosure h).trans oddCore_normalClosure.symm,
    oddCore_normalClosure, hinj, hinj2, hθt, hsimp, ⟨e', fun X => by rw [he', hke]⟩, hCt, hle,
    hn, hCC, hstd,
    not_normal_map h, hsyl, standardComponentOddCore_quotient_eq_bot F, hO2, hFit, hDE, hCD,
    map_normalClosure_S, quotient_normalClosure h, halt, hcat,
    fun hV => ⟨isSimpleGroup_layer h hV, @hcat (isSimpleGroup_layer h hV)⟩,
    ρ, fun c X => ?_, hρker, hρinn, hι, hcyc, hcard⟩
  change QuotientGroup.mk' _ (hk (ρ c X)) = (c : F ⧸ R) * QuotientGroup.mk' _ (hk X) * (c : F ⧸ R)⁻¹
  rw [hke, hke, ← he', ← he', hρ]

end TorusLayer

end CFSG.LocalAnalysis.SymplecticFourStandard
