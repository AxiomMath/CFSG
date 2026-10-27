module

public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.Asc81cPfBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

section Helpers

private theorem w16g_zpow_eq_one_or_self_of_sq {M : Type*} [Group M] {x : M} (hx : x * x = 1)
    (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem w16g_commSub_zpowers_eq_map_of_sq_one (hW : ∀ w : W, w ^ 2 = 1)
    {I : Subgroup W} {y : MulAut W} (hy : y * y = 1) :
    commSub I (Subgroup.zpowers y) = I.map (commHom y) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases w16g_zpow_eq_one_or_self_of_sq hy k with h | h
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨1, I.one_mem, by simp [commHom_apply]⟩
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  · rintro c ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, w, hw, rfl⟩

private theorem w16g_commSub_top_sup_le (X Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (X ⊔ Y) ≤
      commSub (⊤ : Subgroup W) X ⊔ commSub (⊤ : Subgroup W) Y := by
  have h := CFSG.Quasithin.Asc81c.Pf.commSub_iSup (fun b : Bool => cond b X Y)
  rw [iSup_bool_eq, iSup_bool_eq] at h
  exact h.le

end Helpers

theorem rk_eq_rk_commSub_add_rk_inf_fixV (hW : ∀ w : W, w ^ 2 = 1) {I : Subgroup W}
    {y : MulAut W} (hy : y * y = 1) :
    rk ↥I = rk ↥(commSub I (Subgroup.zpowers y)) + rk ↥(I ⊓ fixV (Subgroup.zpowers y)) := by
  have hmap : commSub I (Subgroup.zpowers y) = I.map (commHom y) :=
    w16g_commSub_zpowers_eq_map_of_sq_one hW hy
  have h := rk_map_add_rk_inf_ker (commHom y) I
  rw [← hmap, ker_commHom] at h
  omega

theorem rk_commSub_zpowers_conj (hW : ∀ w : W, w ^ 2 = 1) (y g : MulAut W) :
    rk ↥(commSub ⊤ (Subgroup.zpowers (g⁻¹ * y * g))) = rk ↥(commSub ⊤ (Subgroup.zpowers y)) := by
  have hzp : Subgroup.zpowers (g⁻¹ * y * g) = CFSG.Quasithin.conjBy g⁻¹ (Subgroup.zpowers y) := by
    simp only [CFSG.Quasithin.conjBy, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  have h := commSub_conjBy g⁻¹ (⊤ : Subgroup W) (Subgroup.zpowers y)
  rw [Subgroup.map_top_of_surjective (g⁻¹).toMonoidHom (EquivLike.surjective g⁻¹)] at h
  rw [hzp, h]
  unfold rk
  rw [Subgroup.card_map_of_injective (f := (g⁻¹).toMonoidHom) (g⁻¹).injective]

theorem rk_commSub_zpowers_conj_mul_le (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (g : MulAut W) :
    rk ↥(commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹ * t))) ≤
      2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  have hle : Subgroup.zpowers (g * t * g⁻¹ * t) ≤
      Subgroup.zpowers (g * t * g⁻¹) ⊔ Subgroup.zpowers t := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers (g * t * g⁻¹)) (Subgroup.mem_zpowers t)
  have hcomm : commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹ * t)) ≤
      commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹)) ⊔ commSub ⊤ (Subgroup.zpowers t) := by
    calc commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹ * t))
        ≤ commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹) ⊔ Subgroup.zpowers t) :=
          commSub_mono le_rfl hle
      _ ≤ commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹)) ⊔ commSub ⊤ (Subgroup.zpowers t) :=
          w16g_commSub_top_sup_le _ _
  have hrk := rk_mono hcomm
  have hsup : rk ↥(commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹)) ⊔
      commSub ⊤ (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹))) +
        rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    have h := rk_sup_add_rk_inf (commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹)))
      (commSub ⊤ (Subgroup.zpowers t))
    omega
  have hconj : rk ↥(commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹))) =
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    have h := rk_commSub_zpowers_conj hW t g⁻¹
    rwa [inv_inv] at h
  omega
end CFSG.LocalAnalysis.WeakClosure81
