module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.Quasithin.Vol2.Ch3T325A
public import CFSG.Quasithin.Vol2.Ch3T325G

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

section Aux

variable {G : Type*} [Group G]

theorem mem_cComp_of_quasisimple {K X : Subgroup G} (hq : CFSG.IsQuasisimple ↥K)
    (hK : IsSubnormal K X) : K ∈ cComp X := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨?_, hperf, hK, ?_⟩
  · intro hb
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot K).mp this hb
  · intro K' hlt hne hperf' hsub
    have hKX : K ≤ X := A3.subnormal_le hK
    have hsubK : IsSubnormal K' K := A3.subnormal_of_le_of_le hsub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with h1 | h1
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hPK)
    · apply hne
      rw [← hperf', Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      have hxP : x ∈ P := hK'P hx
      have hxc := Subgroup.mem_center_iff.mp
        (h1 (show (⟨x, hPK.le hxP⟩ : ↥K) ∈ P.subgroupOf K from hxP))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hlt.le hy⟩)

theorem map_subgroupOf_conjAct {A X H : Subgroup G} (hXH : X ≤ H)
    (hH : H ≤ Subgroup.normalizer (A : Set G)) :
    (X.subgroupOf H).map ((conjAct A).comp (Subgroup.inclusion hH)) = autOn X A := by
  ext φ
  constructor
  · rintro ⟨⟨x, hxH⟩, hxX, rfl⟩
    exact ⟨⟨x, hH hxH⟩, hxX, rfl⟩
  · rintro ⟨⟨x, hxN⟩, hxX, rfl⟩
    exact ⟨⟨x, hXH hxX⟩, hxX, rfl⟩

end Aux

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem not_le_centralizer_VM : ¬ L ≤ Subgroup.centralizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) := by
  intro h
  apply c.V₀_ne_bot
  rw [← c.comm_V₀, eq_bot_iff, Subgroup.commutator_le]
  intro v hv l hl
  have := Subgroup.mem_centralizer_iff.1 (h hl) v ((V₀_le_V T V₀).trans (V_le_VM T L V₀) hv)
  rw [Subgroup.mem_bot, commutatorElement_def, this]
  group

theorem quasi_LVM : CFSG.IsQuasisimple ↥(autOn L
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) := by
  refine isQuasisimple_autOn (Subgroup.le_normalizer.trans (M_le_NVM T L V₀))
    c.fsu.quasisimple (fun x hx => c.pCoreOf_L_le ⟨x, ?_, rfl⟩) ?_
  · try with_reducible rfl
    exact hx
  · by_contra hcon
    push Not at hcon
    exact c.not_le_centralizer_VM fun l hl => hcon l hl

theorem orbSup_eq [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (L : Set G)))] :
    orbSup (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
        (V₀.subgroupOf (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) =
      (conjClosure V₀ T).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := by
  have hVVM := V_le_VM T L V₀
  have hTVM := c.T_le_M.trans (M_le_NVM T L V₀)
  rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA T)]
  apply Subgroup.map_injective (conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (L : Set G))).subtype_injective
  rw [map_biSup_smul hTVM, Subgroup.map_subgroupOf_eq_of_le ((V₀_le_V T V₀).trans hVVM),
    Subgroup.map_subgroupOf_eq_of_le hVVM]

end Ctx

end CFSG.Quasithin.H13.T325
