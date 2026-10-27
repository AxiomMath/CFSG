module

public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.SymScalar

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU

theorem kf1215Scalar1 : KF1215Scalar 1 := by
  intro G _ _ p A c L E ctx hmodel n hn
  have hcore := ctx.table_core
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r1ctx hcore hmodel
  have hp := hcore.prime
  have h5 := hcore.five_le
  have hp2 : p ≠ 2 := by omega
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB hn
  have hnF := ctx.mem_normalizer_inf hn
  obtain ⟨l, hlF, hlL, e, he⟩ := S.exists_scalar_of_normalizes hp hp2 (by norm_num) hζ
    (fun α hα _ => perm_three_aut_inner α hα) hnL hnF
  refine ⟨l, ⟨hlL, ctx.mem_torusNormalizer hlL hlF⟩, e, fun f hf => ?_⟩
  have h4 := congrArg Subtype.val (he ⟨f, hf⟩)
  have h3 : ((((E ⊓ L).normalizerMonoidHom ⟨l, hlF⟩ * (E ⊓ L).normalizerMonoidHom ⟨n, hnF⟩)
      ⟨f, hf⟩ : ↥(E ⊓ L)) : G) = l * (n * f * n⁻¹) * l⁻¹ := rfl
  rw [h3, Subgroup.coe_pow] at h4
  calc (l * n) * f * (l * n)⁻¹ = l * (n * f * n⁻¹) * l⁻¹ := by group
    _ = f ^ e := h4

end CFSG.RankThree.PartOne
