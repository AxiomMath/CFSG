module

public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.R9Final
public import CFSG.RankThree.PartOne.KF.SymScalar

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU

theorem kf1215Scalar9_of_inputs (hZ : PSUFourEvenCenterTrivial) : KF1215Scalar 9 := by
  intro G _ _ p A c L E ctx hmodel n hn
  obtain ⟨f, K, hKf, ⟨C⟩⟩ := exists_r9ctx hZ ctx.table_core hmodel
  have hKfin : Finite K := C.hU.finite
  have hζ := C.exists_unit_root
  have hp2 : p ≠ 2 := by have := C.h5; omega
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB hn
  have hnF := ctx.mem_normalizer_inf hn
  obtain ⟨l, hlF, hlL, e, he⟩ := C.toSymCtx.exists_scalar_of_normalizes C.hp hp2 (by norm_num) hζ
    (fun α hα _ => perm_four_aut_inner α hα) hnL hnF
  refine ⟨l, ⟨hlL, ctx.mem_torusNormalizer hlL hlF⟩, e, fun f hf => ?_⟩
  have h4 := congrArg Subtype.val (he ⟨f, hf⟩)
  have h3 : ((((E ⊓ L).normalizerMonoidHom ⟨l, hlF⟩ * (E ⊓ L).normalizerMonoidHom ⟨n, hnF⟩)
      ⟨f, hf⟩ : ↥(E ⊓ L)) : G) = l * (n * f * n⁻¹) * l⁻¹ := rfl
  rw [h3, Subgroup.coe_pow] at h4
  calc (l * n) * f * (l * n)⁻¹ = l * (n * f * n⁻¹) * l⁻¹ := by group
    _ = f ^ e := h4

theorem kf1215Scalar9_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF1215Scalar 9 :=
  kf1215Scalar9_of_inputs (psuFourEvenCenterTrivial_of_multipliers hGA)

end CFSG.RankThree.PartOne
