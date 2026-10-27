module

public import CFSG.Quasithin.Background.G2Relaxed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G]

structure AlmostSpecialCoreBase (V V₁ L T H : Subgroup G) : Prop where
  ne_bot : V₁ ≠ ⊥
  le_V : V₁ ≤ V
  oTwo_eq : L = oTwoUpper L
  V_le_T : V ≤ T
  T_le_normV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  T_le_normL : T ≤ Subgroup.normalizer (L : Set G)
  sylow_LT : IsSylowTwoOf T (L ⊔ T)
  lOne_sup_le : lOne L V₁ ⊔ T ≤ H

theorem AlmostSpecialBase.toCoreBase {V V₁ L T H : Subgroup G}
    (h : AlmostSpecialBase V V₁ L T H) : AlmostSpecialCoreBase V V₁ L T H :=
  ⟨h.ne_bot, h.le_V, h.oTwo_eq, h.V_le_T, h.T_le_normV₁, h.T_le_normL, h.sylow_LT,
    h.lOne_sup_le⟩

theorem AlmostSpecialHyp.toCoreBase {V V₁ L T H : Subgroup G}
    (h : AlmostSpecialHyp V V₁ L T H) : AlmostSpecialCoreBase V V₁ L T H :=
  h.toBase.toCoreBase

namespace AlmostSpecialCoreBase

variable {V V₁ L T H : Subgroup G} (hb : AlmostSpecialCoreBase V V₁ L T H)

include hb

theorem T_le_H : T ≤ H := le_sup_right.trans hb.lOne_sup_le

theorem isPGroup_T : IsPGroup 2 T := hb.sylow_LT.2.1

theorem V_le_N : V ≤ Subgroup.normalizer (V₁ : Set G) := hb.V_le_T.trans hb.T_le_normV₁

theorem conjClosure_le_N (hg : G22Conclusion V V₁ T H) :
    conjClosure V H ≤ Subgroup.normalizer (V₁ : Set G) :=
  hg.three.1.trans hb.T_le_normV₁

theorem G22_commutator_mem (hg : G22Conclusion V V₁ T H) {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ conjClosure V H) : x * y * x⁻¹ * y⁻¹ ∈ V₁ := by
  have hU := hg.one.2
  have hcc := hb.conjClosure_le_N hg
  have hmemY : ∀ u (hu : u ∈ conjClosure V H),
      tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hyQ : tmk V₁ ⟨y, hcc hy⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
    omegaOneCenterOf_le _ (hmemY y hy)
  have hxy : tmk V₁ ⟨x, hcc hx⟩ * tmk V₁ ⟨y, hcc hy⟩ =
      tmk V₁ ⟨y, hcc hy⟩ * tmk V₁ ⟨x, hcc hx⟩ :=
    (mem_centralizer_of_mem_omegaOneCenterOf (hmemY x hx) hyQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem G22_sq_mem (hg : G22Conclusion V V₁ T H) {x : G} (hx : x ∈ conjClosure V H) :
    x ^ 2 ∈ V₁ := by
  have hU := hg.one.2
  have hcc := hb.conjClosure_le_N hg
  have h1 := sq_eq_one_of_mem_omegaOneCenterOf ((secImg_le_iff.1 hU) ⟨x, hcc hx⟩ hx)
  rw [← map_pow] at h1
  simpa using secMk_eq_one_iff.1 h1

theorem VL_le_LT : conjClosure V₁ L ≤ L ⊔ T :=
  conjClosure_le fun _ hl _ hv =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ T) hl)
      (hb.V_le_T.trans le_sup_right (hb.le_V hv))) (inv_mem ((le_sup_left : L ≤ L ⊔ T) hl))

theorem VL_ne_bot : conjClosure V₁ L ≠ ⊥ := fun h =>
  hb.ne_bot (le_bot_iff.1 (h ▸ (le_conjClosure V₁ L)))

end AlmostSpecialCoreBase

end CFSG.Quasithin
