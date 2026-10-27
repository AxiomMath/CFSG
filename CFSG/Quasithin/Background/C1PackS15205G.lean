module

public import CFSG.Quasithin.Background.C1PackS15205F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Facts

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ Yh : Subgroup G}

omit [Finite G] in
theorem Y2of_idem (T Mc M₁ Yh : Subgroup G) :
    oTwoUpper (Y2of T Mc M₁ Yh) = Y2of T Mc M₁ Yh := by
  unfold Y2of
  exact C1Pack153.oTwoUpper_idem' _

theorem Ctr5.exists_QD5 (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁) :
    ∃ Q : Subgroup (MulAut (V154 T Mc M)), QD5 T Mc M M₁ Q := by
  obtain ⟨Q, h1, h2, h3, h4⟩ := c.exists_Qbar hOm
  exact ⟨Q, ⟨h1, h2, h3, h4⟩⟩

theorem Ctr5.pCoreOf_M₁_le_normalizer (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    pCoreOf 2 M₁ ≤ Subgroup.normalizer (Yh : Set G) :=
  (c.pCoreOf_M₁_le_T.trans c.T_le_H).trans hY.H_norm

theorem Ctr5.Y2_le_Yh (c : Ctr5 T Mc M M₁) (hY : Yd5 T Mc M M₁ Yh) :
    Y2of T Mc M₁ Yh ≤ Yh := by
  have h := (c.Y2_le_comm hY).trans (c.comm_le hY)
  refine (Y2of_idem T Mc M₁ Yh).symm.le.trans (oTwoUpper_le_of_pow_mem fun y hy => ?_)
  exact C1Pack153.exists_pow_mem_of_mem_sup_two (pCoreOf_isPGroup 2 _)
    (c.pCoreOf_M₁_le_normalizer hY) (h hy)

theorem Ctr5.Y2_eq_of_two_group (h113 : StageLemma14113) (c : Ctr5 T Mc M M₁)
    (hY : Yd5 T Mc M M₁ Yh) (hO : oTwoUpper Yh = Yh)
    (h2 : ∀ κ ∈ Yh ⊓ Subgroup.centralizer (VZ T M₁ : Set G), ∃ k : ℕ, κ ^ 2 ^ k = 1) :
    Y2of T Mc M₁ Yh = Yh := by
  refine le_antisymm (c.Y2_le_Yh hY) ?_
  refine hO.symm.le.trans (oTwoUpper_le_of_pow_mem fun y hy => ?_)
  have hyM₁ : y ∈ M₁ := (hY.le_H hy).1
  have hyN : y ∈ Subgroup.normalizer (VZ T M₁ : Set G) := le_normalizer_VZ T M₁ hyM₁
  have hmem : conjAct (VZ T M₁) ⟨y, hyN⟩ ∈ autOn (Y2of T Mc M₁ Yh) (VZ T M₁) := by
    rw [c.Y2_autOn h113 hY]
    exact mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩
  obtain ⟨w, hwN, hwY, hwy⟩ := mem_autOn_iff_exists.mp hmem
  have hκ : w⁻¹ * y ∈ Subgroup.centralizer (VZ T M₁ : Set G) := by
    have h3 : conjAct (VZ T M₁) ((⟨w, hwN⟩ : Subgroup.normalizer (VZ T M₁ : Set G))⁻¹ *
        ⟨y, hyN⟩) = 1 := by
      rw [map_mul, map_inv, hwy]
      exact inv_mul_cancel _
    exact A4.conjAct_eq_one_iff.mp h3
  have hwYh : w ∈ Yh := c.Y2_le_Yh hY hwY
  have hκY : w⁻¹ * y ∈ Yh := Yh.mul_mem (Yh.inv_mem hwYh) hy
  obtain ⟨k, hk⟩ := h2 _ ⟨hκY, hκ⟩
  have hκN : w⁻¹ * y ∈ Subgroup.normalizer (Y2of T Mc M₁ Yh : Set G) :=
    c.Y2_normal hY (hY.le_H hκY).1
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hwY hκN (2 ^ k)
  refine ⟨k, ?_⟩
  have e : y = w * (w⁻¹ * y) := by group
  rw [e, hpow, hk, mul_one]
  exact hx'

theorem Ctr5.false_of_Six (h113 : StageLemma14113) (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁)
    (hSix : Case1512Six T Mc M) : False := by
  obtain ⟨Q, hQ⟩ := c.exists_QD5 hOm
  obtain ⟨hY, hC1⟩ := yd5_of_Six hOm c hSix hQ
  have hO : oTwoUpper (yOf152 T Mc M) = yOf152 T Mc M := by
    unfold yOf152
    exact C1Pack153.oTwoUpper_idem' _
  have hY2 : Y2of T Mc M₁ (yOf152 T Mc M) = yOf152 T Mc M := by
    refine c.Y2_eq_of_two_group h113 hY hO fun κ hκ => ?_
    exact (pCoreOf_isPGroup 2 M ⟨κ, hC1 hκ⟩).imp (fun k hk => by simpa using congrArg Subtype.val hk)
  exact c.false_of_Y2_normal h113 hY (by rw [hY2]; exact c.std.c1523.normal)

end Facts

end C1Pack5

end CFSG.Quasithin
