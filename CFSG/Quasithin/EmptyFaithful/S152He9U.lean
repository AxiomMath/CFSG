module

public import CFSG.Quasithin.EmptyFaithful.S152He9T
public import CFSG.Quasithin.EmptyFaithful.S152He9G

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem Y_le_G₀ {T Mc M K₁ : Subgroup G} : yOf152 T Mc M ≤ g0Of T Mc M K₁ :=
  (Y_le_l1.trans le_sup_left).trans le_sup_left

theorem K₁_le_G₀ {T Mc M K₁ : Subgroup G} : K₁ ≤ g0Of T Mc M K₁ := le_sup_right.trans le_sup_left

theorem S_le_G₀ {T Mc M K₁ : Subgroup G} : sOf T K₁ ≤ g0Of T Mc M K₁ := le_sup_right

theorem rc_le_G₀ {T Mc M K₁ : Subgroup G} : rcOf Mc M ≤ g0Of T Mc M K₁ :=
  rc_le_l1.trans (le_sup_left.trans le_sup_left)

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem T_le_normalizer_S : T ≤ Subgroup.normalizer (sOf T K₁ : Set G) := by
  have hidx : ((sOf T K₁).subgroupOf T).index = 2 := c.wr.relIndex_S c.hT
  have hn : ((sOf T K₁).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer S_le_T).1 hn

theorem isUniqueM_YT (h15206 : StageLemma15206) (h15207 : StageLemma15207) :
    IsUniqueM (yOf152 T Mc M ⊔ T) M := by
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M c.hs
  exact (h15207 G T Mc M c.hs Y₁ hY₁).unique

theorem sylow_G₀ (hJ : thompsonJ T ≤ sOf T K₁) (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M)
    (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥) :
    IsSylowTwoOf (sOf T K₁) (Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G)) ∧
      IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) := by
  have hN : g0Of T Mc M K₁ ≤ Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hS := c.sylow_normalizer hJ hU (pCoreOf_isPGroup 2 _) hne (Y_le_G₀.trans hN)
    (K₁_le_G₀.trans hN) (S_le_G₀.trans hN)
  exact ⟨hS, A4.isSylowTwoOf_mono hS S_le_G₀ hN⟩

theorem charTwo_G₀ (hJ : thompsonJ T ≤ sOf T K₁) (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M)
    (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥)
    (hP : pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁)) : CharTwo (g0Of T Mc M K₁) := by
  obtain ⟨hSN, -⟩ := c.sylow_G₀ hJ hU hne
  have hN : g0Of T Mc M K₁ ≤ Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hT2 : IsPGroup 2 T := c.hs.qtfe.sylow.1
  have hUT : pCoreOf 2 (yOf152 T Mc M) ≤ T :=
    c.y.pCoreY_le_rc.trans c.rc_le_T
  have hTU : T ≤ Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G) :=
    c.T_le_normalizer_Y.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hZ := inf_center_ne_bot' hT2 hUT hTU c.y.pCoreY_ne_bot
  have hZ' : pCoreOf 2 (g0Of T Mc M K₁) ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ :=
    fun h => hZ (le_bot_iff.mp (h ▸ inf_le_inf_right _ hP))
  have hTtop : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_le151 c.hs.qtfe.sylow le_top
  have hCN : CharTwo (Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G)) :=
    charTwo_normalizer_of_inf_center c.hs.qtfe.qtke.2.1 hTtop (pCoreOf_isPGroup 2 _) hZ'
  refine charTwo_of_relIndex_le_two hCN hSN hN ?_
  rw [Subgroup.relIndex_eq_one.mpr S_le_G₀]
  norm_num

end Ctx15204

end CFSG.Quasithin.He9
