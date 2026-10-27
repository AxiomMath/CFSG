module

public import CFSG.Quasithin.EmptyFaithful.S146P4
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1
public import CFSG.Quasithin.EmptyFaithful.S152He9Z

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_center_ne_bot' {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyU : (y : G) ∈ U := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hyU, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem yOf152_eq_oTwoUpper (T Mc M : Subgroup G) : yOf152 T Mc M = oTwoUpper (yOf152 T Mc M) := by
  unfold yOf152
  exact (oTwoUpper_idem_P _).symm

namespace YCtx

variable {T Mc M : Subgroup G} (c : YCtx T Mc M)

include c

theorem hVM : V154 T Mc M ≤ M := c.data.h1515.reduced.1

theorem pCoreY_ne_bot : pCoreOf 2 (yOf152 T Mc M) ≠ ⊥ := by
  have hne : autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ := by
    intro h
    have := c.card_five
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨y, hyY, hyN, hy1⟩ := exists_conjAct_ne_one_of_autOn_ne_bot hne
  have hyV : y ∉ Subgroup.centralizer (V154 T Mc M : Set G) := fun h =>
    hy1 (A4.conjAct_eq_one_iff.mpr h)
  have hv : ∃ v ∈ V154 T Mc M, y * v ≠ v * y := by
    by_contra hcon
    push Not at hcon
    exact hyV (Subgroup.mem_centralizer_iff.2 fun v hv => (hcon v hv).symm)
  obtain ⟨v, hv, hvy⟩ := hv
  have hV2 : IsPGroup 2 (V154 T Mc M) := B2F.isPGroup_of_isElemAbelian c.data.hV
  have hc : v * y * v⁻¹ * y⁻¹ ∈ V154 T Mc M ⊓ yOf152 T Mc M := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : y * v⁻¹ * y⁻¹ ∈ V154 T Mc M :=
        (Subgroup.mem_normalizer_iff.mp hyN v⁻¹).mp ((V154 T Mc M).inv_mem hv)
      have e : v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
      rw [e]
      exact (V154 T Mc M).mul_mem hv h1
    · have h1 : v * y * v⁻¹ ∈ yOf152 T Mc M :=
        (Subgroup.mem_normalizer_iff.mp (c.normal (c.hVM hv)) y).mp hyY
      exact (yOf152 T Mc M).mul_mem h1 ((yOf152 T Mc M).inv_mem hyY)
  have hle : V154 T Mc M ⊓ yOf152 T Mc M ≤ pCoreOf 2 (yOf152 T Mc M) := by
    refine le_pCoreOf_of_le_normalizer inf_le_right ?_ (hV2.to_le inf_le_left)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨c.hYV hg, Subgroup.le_normalizer hg⟩
  intro hbot
  have := hle hc
  rw [hbot, Subgroup.mem_bot] at this
  apply hvy
  have h2 : v * y * v⁻¹ * y⁻¹ = 1 := this
  calc y * v = (v * y * v⁻¹ * y⁻¹) * (y * v) := by rw [h2, one_mul]
    _ = v * y := by group

theorem normalizer_Y_le : Subgroup.normalizer (yOf152 T Mc M : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G)) :=
    ⟨pCoreOf 2 (yOf152 T Mc M), c.pCoreY_ne_bot, pCoreOf_isPGroup 2 _, rfl⟩
  have hMle : M ≤ Subgroup.normalizer (pCoreOf 2 (yOf152 T Mc M) : Set G) :=
    c.normal.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hM : quasithinIsMaxTwoLocal M := c.data.inM.1
  have heq := hM.2 _ hloc hMle
  exact (normalizer_le_normalizer_pCoreOf 2 _).trans heq.le

end YCtx

end CFSG.Quasithin.He9
