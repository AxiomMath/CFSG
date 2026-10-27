module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import CFSG.Sporadic.Co2Schreier.IndexNine
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar

public section

namespace CFSG.Monster.B

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem b_index_nine_package :
    IndexNinePackage Cbar := by
  classical
  obtain ⟨S, hScoe, hScenter⟩ :=
    (short_centralizer_quotient_sylow_two).1 (Sylow.nonempty (p := 2) (G := Jbar)).some
  let U : Subgroup Cbar := (S : Subgroup Cbar)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U]
    exact S.not_dvd_index
  have hUC : U ≤ Jbar := by
    dsimp only [U]
    rw [hScoe]
    exact Subgroup.map_subtype_le _
  have hz_mem : xbar ∈ U := by
    have hx : xbar ∈ Subgroup.zpowers xbar := Subgroup.mem_zpowers xbar
    rw [← hScenter] at hx
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.mp hx
    exact hz ▸ z.2
  have hcenter : Subgroup.center U = Subgroup.zpowers ⟨xbar, hz_mem⟩ := by
    dsimp only [U]
    apply Subgroup.map_injective (S : Subgroup Cbar).subtype_injective
    rw [MonoidHom.map_zpowers]
    simpa using hScenter
  have hz1 : xbar ≠ 1 := by
    intro h
    have h2 := orderOf_xbar
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hzc : ∀ y ∈ U, xbar * y = y * xbar := by
    intro y hy
    have hxbar_center : (⟨xbar, hz_mem⟩ : ↥U) ∈ Subgroup.center U := by
      rw [hcenter]
      exact Subgroup.mem_zpowers _
    have h := Subgroup.mem_center_iff.mp hxbar_center ⟨y, hy⟩
    exact (congrArg Subtype.val h).symm
  have hcenter_le : ∀ x ∈ U, (∀ y ∈ U, x * y = y * x) → x = 1 ∨ x = xbar := by
    intro x hx hxcomm
    have hxcenter : (⟨x, hx⟩ : ↥U) ∈ Subgroup.center U := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hxcomm y y.2).symm
    rw [hcenter] at hxcenter
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxcenter
    have hxbar_order : orderOf (⟨xbar, hz_mem⟩ : ↥U) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_xbar
    have hmod : (⟨xbar, hz_mem⟩ : ↥U) ^ (k % 2) = (⟨xbar, hz_mem⟩ : ↥U) ^ k := by
      have h := zpow_mod_orderOf (⟨xbar, hz_mem⟩ : ↥U) k
      rw [hxbar_order] at h
      exact h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      have h1' : (⟨x, hx⟩ : ↥U) = 1 := by rw [← hk, ← hmod, h0, zpow_zero]
      exact congrArg Subtype.val h1'
    · right
      have h1' : (⟨x, hx⟩ : ↥U) = (⟨xbar, hz_mem⟩ : ↥U) := by
        rw [← hk, ← hmod, h1, zpow_one]
      exact congrArg Subtype.val h1'
  have hNC : Subgroup.normalizer (U : Set Cbar) ≤ Jbar := by
    have h := CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.normalizer_le_centralizer_of_center
      (R := U) (z := xbar) hz_mem hz1 hzc hcenter_le
    rwa [centralizer_xbar] at h
  let q : ↥Jbar →* (Jbar ⧸ Ebar.subgroupOf Jbar) :=
    QuotientGroup.mk' (Ebar.subgroupOf Jbar)
  let e : (Jbar ⧸ Ebar.subgroupOf Jbar) ≃* ↥CFSG.Sporadic.Co2Cert.co2P :=
    CFSG.Monster.B.Co2Catalog.jbarQuotEquiv.trans CFSG.Sporadic.Co2Cert.co2PermEquiv
  let π : ↥Jbar →* ↥CFSG.Sporadic.Co2Cert.co2P := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Ebar.subgroupOf Jbar) x
    exact ⟨z, by change e (q z) = y; rw [hz, hx]⟩
  have hker : IsPGroup 2 π.ker := by
    have hker_eq : π.ker = Ebar.subgroupOf Jbar := by
      show (e.toMonoidHom.comp q).ker = Ebar.subgroupOf Jbar
      rw [MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective]
      exact QuotientGroup.ker_mk' _
    rw [hker_eq]
    exact IsPGroup.of_equiv Ebar_extraspecial.1.1
      (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).symm
  have hAut : ∀ α : MulAut Cbar, ∃ g : Cbar, ∀ x : Cbar, α x = g * x * g⁻¹ := by
    intro α
    obtain ⟨g, hg⟩ := CFSG.ComponentClassification.BMCase.cbar_inner α
    exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩
  have hΔ : InnerIndexNinePackage ↥CFSG.Sporadic.Co2Cert.co2P :=
    (show IndexNinePackage ↥CFSG.Sporadic.Co2Cert.co2P from
      CFSG.Sporadic.Co2Schreier.co2_index_nine_package).inner
  exact indexNinePackage_of_quotient hAut hU hNC π hπ hker hΔ

end CFSG.Monster.B
