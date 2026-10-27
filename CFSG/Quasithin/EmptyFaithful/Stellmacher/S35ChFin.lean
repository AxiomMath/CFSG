module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem inter_commF : ∀ z z' : Perm (Fin 5), z ≠ z' → z * z = 1 → z ≠ 1 → Perm.sign z = 1 →
    z' * z' = 1 → z' ≠ 1 → Perm.sign z' = 1 → ∀ p : Fin 5, z p = p → z' p = p →
    ∀ w ∈ commF z, w ∈ commF z' → w = 1 ∨ w = vp p := by
  decide +kernel

theorem cen_sub_std : ∀ σ : Perm (Fin 5), σ * zStd = zStd * σ → σ 4 = 4 → σ ∈ S5SylF := by
  decide +kernel

theorem sign_zStd : Perm.sign zStd = 1 := by decide +kernel

theorem zStd_sq : zStd * zStd = 1 := by decide +kernel

theorem sign_zc {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) : Perm.sign (zc D) = 1 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [zc_eq hD (isCentInv_cj_std_iff.mpr rfl : IsCentInv (cj g S5Syl) (g * zStd * g⁻¹))]
  simp [sign_zStd]

theorem zc_sq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) : zc D * zc D = 1 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have h := zc_eq hD (isCentInv_cj_std_iff.mpr rfl : IsCentInv (cj g S5Syl) (g * zStd * g⁻¹))
  rw [h]
  calc g * zStd * g⁻¹ * (g * zStd * g⁻¹) = g * (zStd * zStd) * g⁻¹ := by group
    _ = 1 := by rw [zStd_sq]; group

theorem sylow_eq_of_zc_eq {D D' : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hD' : Nat.card D' = 8) (hp : fixPt D = fixPt D') (hz : zc D = zc D') : D = D' := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hp' : fixPt (cj g S5Syl) = g 4 := fixPt_eq hD (isFixPt_cj_std_iff.mpr rfl)
  have hz' : zc (cj g S5Syl) = g * zStd * g⁻¹ :=
    zc_eq hD (isCentInv_cj_std_iff.mpr rfl : IsCentInv (cj g S5Syl) (g * zStd * g⁻¹))
  refine (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (by rw [hD, hD'])).symm
  have h1 := (isCentInv_zc hD').2.2 d hd
  have h2 := isFixPt_fixPt hD' d hd
  rw [← hz, hz'] at h1
  rw [← hp, hp'] at h2
  have h3 : g⁻¹ * d * g ∈ S5SylF := by
    refine cen_sub_std _ ?_ ?_
    · calc g⁻¹ * d * g * zStd = g⁻¹ * (d * (g * zStd * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * zStd * g⁻¹) * d) * g := by rw [h1]
        _ = zStd * (g⁻¹ * d * g) := by group
    · simp [Perm.mul_apply, h2]
  rw [mem_cj]
  exact (mem_S5Syl_iff _).mpr h3

theorem inf_commW_le_vp {D D' : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hD' : Nat.card D' = 8) (hp : fixPt D = fixPt D') (hne : D ≠ D') :
    commW orth (Subgroup.zpowers (zc D)) ⊤ ⊓ commW orth (Subgroup.zpowers (zc D')) ⊤ ≤
      Subgroup.zpowers (vp (fixPt D)) := by
  have hzne : zc D ≠ zc D' := fun h => hne (sylow_eq_of_zc_eq hD hD' hp h)
  have hc := isCentInv_zc hD
  have hc' := isCentInv_zc hD'
  intro w hw
  have h1 := (mem_commW_zpowers_iff _ _).mp hw.1
  have h2 := (mem_commW_zpowers_iff _ _).mp hw.2
  have hz1 : zc D (fixPt D) = fixPt D := isFixPt_fixPt hD _ hc.1
  have hz2 : zc D' (fixPt D) = fixPt D := by
    rw [hp]; exact isFixPt_fixPt hD' _ hc'.1
  rw [mem_zpowers_iff_of_mul_self (vp_mul_self _)]
  exact inter_commF _ _ hzne (zc_sq hD) hc.2.1 (sign_zc hD) (zc_sq hD') hc'.2.1 (sign_zc hD')
    _ hz1 hz2 w h1 h2

theorem swap_mem_That {D : Subgroup (Perm (Fin 5))} {σ : Perm (Fin 5)} (hσ : σ ∈ D)
    (hs : σ.IsSwap) : σ ∈ That D := Subgroup.subset_closure ⟨hσ, hs⟩

theorem zc_not_isSwap {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ¬ (zc D).IsSwap := by
  intro h
  rw [isSwap_iff] at h
  exact h.2.2 (sign_zc hD)

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
