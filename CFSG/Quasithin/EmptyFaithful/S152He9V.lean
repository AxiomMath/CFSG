module

public import CFSG.Quasithin.EmptyFaithful.S152He9U
public import CFSG.Quasithin.EmptyFaithful.S153D0Rad

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rOf (T Mc M K₁ : Subgroup G) : Subgroup G :=
  pCoreOf 2 (yOf152 T Mc M ⊔ sOf T K₁)

theorem normalizer_le_of_YT {Y T M D : Subgroup G} (hU : IsUniqueM (Y ⊔ T) M) (hD2 : IsPGroup 2 D)
    (hD1 : D ≠ ⊥) (hY : Y ≤ Subgroup.normalizer (D : Set G))
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : Subgroup.normalizer (D : Set G) ≤ M := by
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (D : Set G)) ⟨D, hD1, hD2, rfl⟩
  have hEq : M'' = M := hU.2 M'' ⟨hM'', (sup_le hY hT).trans hle⟩
  exact hEq ▸ hle

theorem YS_le_normalizer_R {T Mc M K₁ : Subgroup G} : yOf152 T Mc M ⊔ sOf T K₁ ≤
    Subgroup.normalizer (rOf T Mc M K₁ : Set G) := le_normalizer_pCoreOf 2 _

theorem R_isPGroup {T Mc M K₁ : Subgroup G} : IsPGroup 2 (rOf T Mc M K₁) := pCoreOf_isPGroup 2 _

theorem Y_le_normalizer_R {T Mc M K₁ : Subgroup G} :
    yOf152 T Mc M ≤ Subgroup.normalizer (rOf T Mc M K₁ : Set G) :=
  le_sup_left.trans YS_le_normalizer_R

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem S_le_normalizer_Y : sOf T K₁ ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  S_le_T.trans c.T_le_normalizer_Y

theorem R_ne_bot : rOf T Mc M K₁ ≠ ⊥ := by
  intro hbot
  apply c.y.pCoreY_ne_bot
  have hle : pCoreOf 2 (yOf152 T Mc M) ≤ rOf T Mc M K₁ := by
    refine le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 _).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)
    refine sup_le (le_normalizer_pCoreOf 2 _) ?_
    exact c.S_le_normalizer_Y.trans (normalizer_le_normalizer_pCoreOf 2 _)
  exact le_bot_iff.mp (hbot ▸ hle)

theorem sylow_S_YS : IsSylowTwoOf (sOf T K₁) (yOf152 T Mc M ⊔ sOf T K₁) := by
  obtain ⟨r, hr, y, hy, hnot⟩ := c.y.nt
  exact (oTwoQuot_sup_iso c.S_pgroup c.S_le_normalizer_Y c.y.relIndex_five
    (c.y.pCoreY_le_rc.trans c.rc_le_S) ⟨r, c.rc_le_S hr, y, hy, hnot⟩).1

theorem R_le_S : rOf T Mc M K₁ ≤ sOf T K₁ :=
  A4.le_of_normal_of_isSylowTwoOf c.sylow_S_YS (pCoreOf_le 2 _)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2 YS_le_normalizer_R)
    (pCoreOf_isPGroup 2 _)

theorem T_le_normalizer_R : T ≤ Subgroup.normalizer (rOf T Mc M K₁ : Set G) := by
  have : T ≤ Subgroup.normalizer ((yOf152 T Mc M ⊔ sOf T K₁ : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨c.T_le_normalizer_Y hg, c.T_le_normalizer_S hg⟩
  exact this.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem normalizer_R_le (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M) :
    Subgroup.normalizer (rOf T Mc M K₁ : Set G) ≤ M :=
  normalizer_le_of_YT hU R_isPGroup c.R_ne_bot Y_le_normalizer_R c.T_le_normalizer_R

theorem cgs_le (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M) :
    cgsIn (g0Of T Mc M K₁) (rOf T Mc M K₁) ≤ M ⊓ g0Of T Mc M K₁ := by
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hN : Subgroup.normalizer (C : Set G) ≤ M := by
    refine normalizer_le_of_YT hU (R_isPGroup.to_le hCR) hC1 ?_ ?_
    · exact Y_le_normalizer_R.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
    · exact c.T_le_normalizer_R.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
  exact le_inf (inf_le_right.trans hN) inf_le_left

theorem hypC23 (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M) (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥)
    (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁)) :
    HypC23 (g0Of T Mc M K₁) (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) := by
  have hnorm : g0Of T Mc M K₁ ⊓ Subgroup.normalizer (yOf152 T Mc M : Set G) =
      M ⊓ g0Of T Mc M K₁ :=
    le_antisymm (fun g hg => ⟨c.y.normalizer_Y_le hg.2, hg.1⟩) (fun g hg => ⟨hg.2, c.y.normal hg.1⟩)
  obtain ⟨hsyl, hrad⟩ := S153D.sylow_radical_of_normalizer_le (yOf152_eq_oTwoUpper T Mc M)
    Y_le_G₀ hS c.S_le_M hnorm c.R_ne_bot (c.normalizer_R_le hU)
  have hK := c.hs.qtfe
  exact ⟨sqtkGroup_of_pCoreOf_ne_bot hK.qtke hK.simple hK.nonabelian hne, hrad, inf_le_right,
    c.cgs_le hU, hsyl⟩

end Ctx15204

end CFSG.Quasithin.He9
