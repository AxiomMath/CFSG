module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem std_cen (h : Perm (Fin 5)) (hh : h ∈ S5SylF) (hc : ∀ w ∈ commF zStd, orth.act h w = w) :
    (h = 1 ∨ h = zStd ∨ h = swap 0 2 ∨ h = swap 1 3) ∧
      ∀ w : orth.W, orth.act h w * w⁻¹ ∈ commF zStd := by
  have key : ∀ h ∈ S5SylF, (∀ w ∈ commF zStd, orth.act h w = w) →
      (h = 1 ∨ h = zStd ∨ h = swap 0 2 ∨ h = swap 1 3) ∧
        ∀ w : orth.W, orth.act h w * w⁻¹ ∈ commF zStd := by
    unfold commF zStd; decide +kernel
  exact key h hh hc

theorem std_even_fix (h : Perm (Fin 5)) (h4 : h 4 = 4) (hs : Perm.sign h = 1) (hh : h * h = 1) :
    h ∈ S5SylF := by
  have key : ∀ h : Perm (Fin 5), h 4 = 4 → Perm.sign h = 1 → h * h = 1 → h ∈ S5SylF := by
    decide +kernel
  exact key h h4 hs hh

theorem sign_conj_inv (c g : Perm (Fin 5)) : Perm.sign (c⁻¹ * g * c) = Perm.sign g := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
    one_mul]

theorem zc_cj_std (c : Perm (Fin 5)) : zc (cj c S5Syl) = c * zStd * c⁻¹ :=
  zc_eq (card_cj_S5Syl c) (isCentInv_cj_std_iff.mpr rfl)

theorem mem_plane_iff (c : Perm (Fin 5)) (w : orth.W) :
    w ∈ commW orth (Subgroup.zpowers (c * zStd * c⁻¹)) ⊤ ↔ orth.act c⁻¹ w ∈ commF zStd := by
  rw [← cj_zpowers, commW_cj_top, mem_mp, mem_commW_zpowers_iff]

theorem conj_cen_data {c g : Perm (Fin 5)} (hg : g ∈ cj c S5Syl)
    (hcen : ∀ w ∈ commW orth (Subgroup.zpowers (c * zStd * c⁻¹)) ⊤, orth.act g w = w) :
    c⁻¹ * g * c ∈ S5SylF ∧ ∀ w ∈ commF zStd, orth.act (c⁻¹ * g * c) w = w := by
  refine ⟨(mem_S5Syl_iff _).mp (mem_cj.mp hg), fun w hw => ?_⟩
  have h1 : orth.act c w ∈ commW orth (Subgroup.zpowers (c * zStd * c⁻¹)) ⊤ := by
    rw [mem_plane_iff, act_inv_act]; exact hw
  rw [act_mul_apply, act_mul_apply, hcen _ h1, act_inv_act]

theorem conj_act_comm (c g : Perm (Fin 5)) (w : orth.W) :
    orth.act c⁻¹ (orth.act g w * w⁻¹) =
      orth.act (c⁻¹ * g * c) (orth.act c⁻¹ w) * (orth.act c⁻¹ w)⁻¹ := by
  rw [MulEquiv.map_mul (orth.act c⁻¹), MulEquiv.map_inv (orth.act c⁻¹), act_mul_apply,
    act_mul_apply, act_act_inv]

theorem cen_cases {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {g : Perm (Fin 5)}
    (hg : g ∈ D)
    (hcen : ∀ w ∈ commW orth (Subgroup.zpowers (zc D)) ⊤, orth.act g w = w) :
    g = 1 ∨ g = zc D ∨ g.IsSwap := by
  obtain ⟨c, rfl⟩ := exists_cj hD
  rw [zc_cj_std] at hcen ⊢
  obtain ⟨h1, h2⟩ := conj_cen_data hg hcen
  have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
  rcases (std_cen _ h1 h2).1 with h | h | h | h
  · left; rw [e, h]; group
  · right; left; rw [e, h]
  all_goals
    right; right; rw [e, h, isSwap_conj]
  · exact ⟨0, 2, by decide, rfl⟩
  · exact ⟨1, 3, by decide, rfl⟩

theorem comm_le_of_cen {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {g : Perm (Fin 5)}
    (hg : g ∈ D)
    (hcen : ∀ w ∈ commW orth (Subgroup.zpowers (zc D)) ⊤, orth.act g w = w) (w : orth.W) :
    orth.act g w * w⁻¹ ∈ commW orth (Subgroup.zpowers (zc D)) ⊤ := by
  obtain ⟨c, rfl⟩ := exists_cj hD
  rw [zc_cj_std] at hcen ⊢
  obtain ⟨h1, h2⟩ := conj_cen_data hg hcen
  rw [mem_plane_iff, conj_act_comm]
  exact (std_cen _ h1 h2).2 _

theorem mem_of_even_sq_fix {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {p : Fin 5}
    (hp : IsFixPt D p) {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) (hgg : g * g = 1)
    (hgp : g p = p) : g ∈ D := by
  obtain ⟨c, rfl⟩ := exists_cj hD
  have hpc : p = c 4 := isFixPt_cj_std_iff.mp hp
  subst hpc
  have h4 : (c⁻¹ * g * c) 4 = 4 := by
    simp only [Perm.mul_apply]; rw [hgp]; simp
  have h5 : Perm.sign (c⁻¹ * g * c) = 1 := by
    rw [sign_conj_inv]; exact Perm.mem_alternatingGroup.mp hg
  have h6 : (c⁻¹ * g * c) * (c⁻¹ * g * c) = 1 := by
    calc (c⁻¹ * g * c) * (c⁻¹ * g * c) = c⁻¹ * (g * g) * c := by group
      _ = 1 := by rw [hgg]; group
  exact mem_cj.mpr ((mem_S5Syl_iff _).mpr (std_even_fix _ h4 h5 h6))

theorem even_of_not_swap {g : Perm (Fin 5)} (hg : g * g = 1) (hs : ¬ g.IsSwap) :
    g ∈ alternatingGroup (Fin 5) := by
  have key : ∀ g : Perm (Fin 5), g * g = 1 →
      ¬ (g ≠ 1 ∧ g ^ 2 = 1 ∧ Perm.sign g ≠ 1) → Perm.sign g = 1 := by decide +kernel
  rw [Perm.mem_alternatingGroup]
  exact key g hg (fun h => hs ((isSwap_iff g).mpr h))

theorem card_commW_zc {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (commW orth (Subgroup.zpowers (zc D)) ⊤) = 4 :=
  card_commW_z hD (isCentInv_zc hD)

theorem act_vp_eq_iff (g : Perm (Fin 5)) (p : Fin 5) : orth.act g (vp p) = vp p ↔ g p = p := by
  rw [act_vp]; exact vp_injective.eq_iff

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
