module

public import CFSG.Quasithin.Vol2.Ch3T326P
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Vol2.Ch3T326H

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem inf_eq_bot_of_isSumMod {W : Type} [CommGroup W] {C A B Tot : Subgroup W}
    (h : IsSumMod C A B Tot) (hA : A ⊓ C = ⊥) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff, ← hA]
  exact le_inf inf_le_left
    ((inf_le_inf le_sup_left le_sup_left).trans h.2)

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem inf_fixV_eq_bot (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    (hB48 : D36B48q) (h6 : Vol2.Ch11.TmpL6_3_2_2_six) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    {s : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ T)
    (hDx : D3Std (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))))
    (hlt : (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) <
      orbSup (autOn T (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))))
    (htriv : ∀ v ∈ (CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))),
      ∀ g ∈ conjAutSub (conjAct (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))) ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩)
        (autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))), g v = v)
    (h32 : D36L32
        (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))) :
    (CFSG.conjugate V₀ x).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
      fixV (autOn (conjClosure L T)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) = ⊥ := by
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  have htn := c.not_mem_normalizer hA37 hs hsn
  have hfix := Vol2.Ch11.SecC.B51.fixV_autOn (W := conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))) c.L₀_le_NVM
  have horb := c.orbSup_conjugate hx
  have hVVM := T325.V_le_VM T (conjClosure L T) V₀
  have hXV : conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    sup_le c.L₀_le_NV (T325.T_le_NV T V₀)
  have hXVM := sup_le c.L₀_le_NVM c.T_le_NVM
  have hsup := H13.autOn_sup (V := conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))) c.L₀_le_NVM c.T_le_NVM
  have hexpV : ∀ v : ↥(conjClosure V₀ T), v ^ 2 = 1 :=
    fun v => Subtype.ext (by simpa using c.elemV.2 v v.2)
  by_cases hC : fsuCVM T L V₀ = ⊥
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨-, hvF⟩ := Subgroup.mem_inf.mp hv
    rw [hfix, Subgroup.mem_subgroupOf] at hvF
    have hv : (v : G) ∈ fsuCVM T L V₀ := ⟨v.2, hvF⟩
    rw [hC, Subgroup.mem_bot] at hv
    exact (Subgroup.mem_bot).mpr (Subtype.ext hv)
  · obtain ⟨-, _, hff⟩ := h6 G T L V₀ c.fsu hC c.uniq₀
    have hq1 : qOf (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T)) ≤ 1 :=
      ((B1_4_5 hexpV (autOn (conjClosure L T ⊔ T) (conjClosure V₀ T))).out 1 3).1 hff
    have hq := (kq_le_kq_of_le216 (T325.map_autOn_le_autSub hVVM hXV hXVM) 2).trans
      (T325.kq_map_congr_le (Subgroup.subgroupOfEquivOfLe hVVM).symm _ 2)
    have hq2 : qOf (autSub (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊔
        autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
        (orbSup (autOn T (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          ((CFSG.conjugate V₀ x).subgroupOf
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))))) ≤
        ((2 : ℚ) : WithTop ℚ) := by
      rw [horb, ← hsup]
      refine (hq.trans hq1).trans ?_
      exact_mod_cast (by norm_num : (1 : ℚ) ≤ 2)
    exact hB48 _ _ _ _ _ _ _ hDx hlt
      (Setup.mem_autOn_iff.mpr ⟨⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩, T.inv_mem hs, rfl⟩) htn hMp
      htriv hq2 h32.1 h32.2.1

theorem card_V₀_of_d36L32 [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {x : G} (hx : x ∈ T)
    (h32 : Nat.card ↥((CFSG.conjugate V₀ x).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) =
      2 ^ 3 * Nat.card ↥((CFSG.conjugate V₀ x).subgroupOf
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
        fixV (autOn (conjClosure L T)
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))))
    (hbot : (CFSG.conjugate V₀ x).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) ⊓
      fixV (autOn (conjClosure L T)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) = ⊥) :
    Nat.card V₀ = 2 ^ 3 := by
  have hV₀VM := (T325.V₀_le_V T V₀).trans (T325.V_le_VM T (conjClosure L T) V₀)
  have hxVM : CFSG.conjugate V₀ x ≤ conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) :=
    le_of_le_of_eq (Subgroup.map_mono hV₀VM) (c.conjugate_VM (c.T_le_M hx))
  rw [hbot, Subgroup.card_bot, mul_one,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxVM).toEquiv] at h32
  rw [← h32]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (MulEquiv.injective _)).symm

end Ctx

end CFSG.Quasithin.H13.T326
