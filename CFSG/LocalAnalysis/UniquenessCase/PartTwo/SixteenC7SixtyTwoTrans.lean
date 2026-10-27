module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem s16c7_mkTil_injective (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil ⊥ V hV) := by
  intro x y h
  have h1 := (mkTil_eq_iff ⊥ V hV x y).1 h
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact IntMod.val_injective h1

theorem s16c7_act_mkTil_eq_iff (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : ↥(stabTil ⊥ V)) (x : IntMod V hV) :
    actTil ⊥ V hV g (mkTil ⊥ V hV x) = mkTil ⊥ V hV x ↔
      (g : G) * x.val * (g : G)⁻¹ = x.val := by
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one]

theorem s16c7_mem_fixV_barSub_iff (V : Subgroup G) (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil ⊥ V) (x : IntMod V hV) :
    mkTil ⊥ V hV x ∈ fixV (barSub ⊥ V hV Y) ↔ ∀ y ∈ Y, y * x.val * y⁻¹ = x.val := by
  rw [mem_fixV]
  constructor
  · intro h y hy
    exact (s16c7_act_mkTil_eq_iff V hV ⟨y, hY hy⟩ x).1
      (h _ (actTil_mem_barSub ⊥ V hV hy (hY hy)))
  · intro h φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV Y φ).1 hφ
    exact (s16c7_act_mkTil_eq_iff V hV g x).2 (h _ hg)

theorem s16c7_inf_centralizer_eq_zpowers (V : Subgroup G) (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil ⊥ V) {z : IntMod V hV}
    (h : fixV (barSub ⊥ V hV Y) = Subgroup.zpowers (mkTil ⊥ V hV z)) :
    V ⊓ centralizer (Y : Set G) = Subgroup.zpowers z.val := by
  have hzfix : mkTil ⊥ V hV z ∈ fixV (barSub ⊥ V hV Y) := h ▸ Subgroup.mem_zpowers _
  have hzc : ∀ y ∈ Y, y * z.val * y⁻¹ = z.val :=
    (s16c7_mem_fixV_barSub_iff V hV hY z).1 hzfix
  have hval : ∀ k : ℤ, (z ^ k).val = z.val ^ k := fun k => map_zpow (valHom V hV) z k
  ext v
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hvV, hvc⟩
    set x : IntMod V hV := IntMod.mk hV ⟨v, hvV⟩ with hx
    have hxv : x.val = v := rfl
    have h1 : mkTil ⊥ V hV x ∈ fixV (barSub ⊥ V hV Y) := by
      rw [s16c7_mem_fixV_barSub_iff V hV hY, hxv]
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hvc
      have h2 : v * y = y * v := (hvc y hy).symm
      rw [← h2]
      group
    rw [h] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : z ^ k = x :=
      s16c7_mkTil_injective V hV (by rw [map_zpow]; exact hk)
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← hval k, h2]
    exact hxv
  · intro hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    refine ⟨?_, ?_⟩
    · rw [← hval k]
      exact (z ^ k).val_mem
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hcomm : Commute y z.val := by
        have := hzc y hy
        unfold Commute SemiconjBy
        calc y * z.val = (y * z.val * y⁻¹) * y := by group
          _ = z.val * y := by rw [this]
      exact (hcomm.zpow_right k).eq

theorem s16c7_actTil_eq_one_iff_mem_centralizer (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : ↥(stabTil ⊥ V)) :
    actTil ⊥ V hV g = 1 ↔ (g : G) ∈ centralizer (V : Set G) := by
  rw [actTil_eq_one_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := Subgroup.mem_bot.1 (h v hv)
    have h2 : (g : G) * v * (g : G)⁻¹ = v := by
      rw [mul_inv_eq_one] at h1
      exact h1
    calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * (g : G) := by rw [h2]
      _ = (g : G) * v := by group
  · intro h v hv
    rw [Subgroup.mem_bot]
    have h1 : v * (g : G) = (g : G) * v := h v hv
    calc (g : G) * v * (g : G)⁻¹ * v⁻¹ = (v * (g : G)) * (g : G)⁻¹ * v⁻¹ := by rw [h1]
      _ = 1 := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
