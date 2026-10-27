module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support.S45CircB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitCor
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support.S45CircA

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

theorem hom_zmod_two_eq_one_of_commutator_eq {𝔾 : Type*} [Group 𝔾] {K : Subgroup 𝔾}
    (hK : ⁅K, K⁆ = K) (f : ↥K →* Multiplicative (ZMod 2)) : f = 1 := by
  have hle : ⁅K, K⁆ ≤ f.ker.map K.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥K), ⟨y, hy⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [hK] at hle
  refine MonoidHom.ext fun x => ?_
  obtain ⟨k, hk, hkx⟩ := hle x.2
  rw [MonoidHom.one_apply, ← MonoidHom.mem_ker, show x = k from Subtype.ext hkx.symm]
  simpa using hk

theorem s45C1aQ4_holds : S45C1aQ4 := by
  intro G _ _ M T L F _ _ φ c hq δ hδ
  have h := c.hyp
  have := c.charP
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hδ
  obtain ⟨dual, hV⟩ := exists_isSum_vcirc c hδ hψs hψ
  have hab := isElemAbelian_vi _ h.hyp20 c.bpos (δ := δ) (i := 2) (by rw [c.b8]; norm_num)
  have hVv : Vcirc h.le L δ ≤ Vv (puAmalgam h.le) δ := c.vcirc_le_vv δ
  have hVab : ∀ x ∈ Vcirc h.le L δ, ∀ y ∈ Vcirc h.le L δ, x * y = y * x := by
    intro x hx y hy
    have := hab.1.is_comm.comm ⟨x, hVv hx⟩ ⟨y, hVv hy⟩
    simpa using congrArg Subtype.val this
  have hV2 : ∀ x ∈ Vcirc h.le L δ, x * x = 1 := by
    intro x hx
    have := hab.2 x (hVv hx)
    rwa [pow_two] at this
  exact (OrdinaryProofs.H1SL3.eq_of_isSum_of_commutator_eq hq hψs hV hVab hV2
    (uloc_sup_hloc_le c hδ) (stab_le_normalizer_uloc_sup_hloc c hδ)
    (fun _ ha _ hz => commutator_zm_mem c hδ ha hz.2)
    (fun a ha _ hv => commutator_vcirc_mem_of_ker c hδ hψ a ha hv)
    (ltil_le_stab h δ) rfl (hom_zmod_two_eq_one_of_commutator_eq (ltil_perfect h hδ))).le

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
