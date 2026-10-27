module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
public import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

theorem simple_radical_quotient_of_isCComponent_top {L : Type*} [Group L] [Finite L]
    (h : CFSG.IsCComponent (⊤ : Subgroup L)) :
    IsSimpleGroup (L ⧸ CFSG.solvableRadical L) ∧
      ∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a := by
  have hL : (⊤ : Subgroup L) ∈ cComp (⊤ : Subgroup L) := mem_cComp_top_iff_isCComponent.mpr h
  obtain ⟨-, ⟨hs, a, b, hab⟩, -⟩ := cComp_structure hL
  have hR : ((solvRad (⊤ : Subgroup L)).subgroupOf ⊤).map
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom = CFSG.solvableRadical L := by
    rw [A3.solvableRadical_eq_solvRad_top]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, mem_top x⟩, hx, rfl⟩
  let e := QuotientGroup.congr _ _ (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L) hR
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun hba => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, hba]

section Bar

variable {B : Type*} [Group B] (L : Subgroup B) [L.Normal]

@[expose] def barRestrict : L →* (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) :=
  ((QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)).comp L.subtype).codRestrict _
    fun l => mem_map_of_mem _ l.2

theorem barRestrict_apply (l : L) :
    (barRestrict L l : B ⧸ (CFSG.pCore 2 L).map L.subtype) = ((l : B) : B ⧸ _) := rfl

theorem barRestrict_surjective : Function.Surjective (barRestrict L) := by
  rintro ⟨_, l, hl, rfl⟩
  exact ⟨⟨l, hl⟩, rfl⟩

theorem barRestrict_ker : (barRestrict L).ker = CFSG.pCore 2 L := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : ((l : B) : B ⧸ (CFSG.pCore 2 L).map L.subtype) = 1 := congrArg Subtype.val h
    rw [QuotientGroup.eq_one_iff] at h1
    exact (mem_map_iff_mem L.subtype_injective).mp h1
  · intro h
    apply Subtype.ext
    change ((l : B) : B ⧸ (CFSG.pCore 2 L).map L.subtype) = 1
    rw [QuotientGroup.eq_one_iff]
    exact mem_map_of_mem _ h

theorem map_barRestrict (X : Subgroup L) :
    X.map (barRestrict L) = ((X.map L.subtype).map
      (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subgroupOf
        (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) := by
  ext y
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩

variable [Finite B]

theorem isSolvable_barRestrict_ker : Group.IsSolvable (barRestrict L).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [barRestrict_ker]
  have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).isNilpotent
  infer_instance

@[expose] noncomputable def barEquiv :
    L ⧸ CFSG.pCore 2 L ≃* (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) :=
  (QuotientGroup.quotientMulEquivOfEq (barRestrict_ker L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (barRestrict_surjective L))

theorem bar_setting (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    CFSG.IsStronglyQuasithin (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) ∧
      CFSG.pCore 2 (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) = ⊥ ∧
      CFSG.IsCComponent
        (⊤ : Subgroup (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype)))) ∧
      ¬ CFSG.IsQuasisimple (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) ∧
      CFSG.solvableRadical (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) =
        (((CFSG.solvableRadical L).map L.subtype).map
          (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))).subgroupOf
            (L.map (QuotientGroup.mk' ((CFSG.pCore 2 L).map L.subtype))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun r hr hr2 => ?_, ?_, ?_, fun h => hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (barEquiv L).symm h), ?_⟩
  · rw [← CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv (barEquiv L) r,
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr _
        (CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hr hr2)]
    exact hSQT r hr hr2
  · rw [← CFSG.LieType.SteinbergBR.pCore_map_equiv 2 (barEquiv L),
      CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
  · have h := map_mem_cComp_top (barRestrict L) (barRestrict_surjective L)
      (isSolvable_barRestrict_ker L) (mem_cComp_top_iff_isCComponent.mpr hLC)
    rw [map_top_of_surjective _ (barRestrict_surjective L)] at h
    exact mem_cComp_top_iff_isCComponent.mp h
  · rw [← CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
      (barRestrict_surjective L) (isSolvable_barRestrict_ker L), map_barRestrict]

end Bar

end CFSG.Quasithin.H13.NQBlock
