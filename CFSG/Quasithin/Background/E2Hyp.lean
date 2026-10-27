module

public import CFSG.Quasithin.Background.E2Fifteen
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type} [Group G] [Finite G]

structure Hyp28 (H T M V : Subgroup G) : Prop where
  minParabolic : MinParabolic H T M
  sqtk : SQTKGroup ↥H
  le_T : V ≤ T
  normal_T : T ≤ Subgroup.normalizer (V : Set G)
  elem : IsElemAbelian 2 V
  le_pCoreOf : V ≤ pCoreOf 2 M
  not_le_kerIn : ¬ V ≤ kerIn M H

namespace Hyp28

variable {H T M V : Subgroup G}

theorem le_H (h : Hyp28 H T M V) : V ≤ H := h.le_T.trans h.minParabolic.isSylow.1

theorem not_le_pCoreOf (h : Hyp28 H T M V) : ¬ V ≤ pCoreOf 2 H := fun hle =>
  h.not_le_kerIn (hle.trans h.minParabolic.pCoreOf_le_kerIn)

theorem ne_bot (h : Hyp28 H T M V) : V ≠ ⊥ := fun h1 => h.not_le_kerIn (h1 ▸ bot_le)

theorem not_le_normalizer (h : Hyp28 H T M V) : ¬ H ≤ Subgroup.normalizer (V : Set G) := by
  intro hHV
  apply h.not_le_pCoreOf
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V H h.le_H
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le_H).2 hHV)
    (B6.isPGroup_of_isElemAbelian h.elem)

theorem inf_normalizer_le (h : Hyp28 H T M V) : H ⊓ Subgroup.normalizer (V : Set G) ≤ M :=
  h.minParabolic.le_of_lt (le_inf h.minParabolic.isSylow.1 h.normal_T)
    (lt_of_le_of_ne inf_le_left fun heq => h.not_le_normalizer (heq ▸ inf_le_right))

theorem e2_13_two (h : Hyp28 H T M V) (hsolv : Group.IsSolvable H) (hchar : CharTwo H) :
    ∃ g ∈ H, ∃ A : Subgroup G, A ≤ T ∧ A ≤ cjSub g V ∧ IsElemAbelian 2 A ∧
      ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) ∧
      A ⊓ Subgroup.centralizer (V : Set G) = V ⊓ cjSub g V ∧
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
        ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2 :=
  E2_13_two_of_isSolvable h.minParabolic hsolv hchar h.le_T h.normal_T h.elem h.not_le_kerIn

theorem e2_13_three (h : Hyp28 H T M V) (hsolv : Group.IsSolvable H) (hchar : CharTwo H) :
    qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ) :=
  E2_13_three_of_isSolvable h.elem h.minParabolic hsolv hchar h.le_T h.normal_T h.not_le_kerIn

theorem e2_15 (h : Hyp28 H T M V) (hsolv : Group.IsSolvable H) (hchar : CharTwo H) :
    qhatOf (autI h.elem H) < ((2 : ℚ) : WithTop ℚ) :=
  E2_15_of_isSolvable h.elem h.minParabolic hsolv hchar h.le_T h.normal_T h.not_le_kerIn

end Hyp28

@[expose] noncomputable def dParam (q : ℕ) : ℕ := orderOf (2 : ZMod q)

@[expose] noncomputable def dParamPrime (q : ℕ) : ℕ :=
  if Even (dParam q) then dParam q / 2 else dParam q

end E2

end CFSG.Quasithin
