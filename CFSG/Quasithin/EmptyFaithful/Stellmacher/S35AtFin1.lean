module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.At

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem commW_mono_left' {B B' : Subgroup (Perm (Fin 5))} (h : B ≤ B') (U : Subgroup orth.W) :
    commW orth B U ≤ commW orth B' U := by
  unfold commW
  refine Subgroup.closure_mono ?_
  rintro _ ⟨b, hb, u, hu, rfl⟩
  exact ⟨b, h hb, u, hu, rfl⟩

theorem std_data {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ∃ g : Perm (Fin 5), D = cj g S5Syl ∧ That D = cj g S5That ∧ zc D = g * zStd * g⁻¹ ∧
      fixPt D = g 4 := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  refine ⟨g, rfl, ?_, ?_, ?_⟩
  · rw [← cj_That, That_std]
  · exact zc_eq (card_cj_S5Syl g) (isCentInv_cj_std_iff.mpr rfl)
  · exact fixPt_eq (card_cj_S5Syl g) (isFixPt_cj_std_iff.mpr rfl)

theorem mem_commW_zStd (w : orth.W) :
    w ∈ commW orth (Subgroup.zpowers zStd) ⊤ ↔ w = 1 ∨ w = ep 0 2 ∨ w = ep 1 3 ∨ w = vp 4 :=
  mem_commW_double (a := 0) (b := 2) (c := 1) (d := 3) (p := 4) (by decide) w

theorem std_cen_iff : ∀ d : Perm (Fin 5),
    (d ∈ S5SylF ∧ ∀ w ∈ commF zStd, orth.act d w = w) ↔ d ∈ S5ThatF := by
  unfold commF zStd; decide +kernel

theorem cenW_commW_inf_std :
    cenW (commW orth (Subgroup.zpowers zStd) ⊤) ⊓ S5Syl = S5That := by
  ext d
  simp only [Subgroup.mem_inf, mem_cenW, mem_S5Syl_iff, mem_S5That_iff, mem_commW_zpowers_iff]
  rw [← std_cen_iff d, and_comm]

theorem zStd_mem_S5That : zStd ∈ S5That := by
  rw [mem_S5That_iff]; unfold zStd; decide +kernel

theorem commW_That_std_le :
    commW orth S5That ⊤ ≤ commW orth (Subgroup.zpowers zStd) ⊤ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro w ⟨b, hb, u, -, rfl⟩
  show _ ∈ commW orth (Subgroup.zpowers zStd) ⊤
  rw [mem_commW_zpowers_iff]
  rw [mem_S5That_iff] at hb
  have key : ∀ b ∈ S5ThatF, ∀ u : orth.W, orth.act b u * u⁻¹ ∈ commF zStd := by
    unfold commF zStd; decide +kernel
  exact key b hb u

theorem cenW_commW_inf_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    cenW (commW orth (Subgroup.zpowers (zc D)) ⊤) ⊓ D = That D := by
  obtain ⟨g, rfl, hT, hz, -⟩ := std_data hD
  rw [hT, hz, ← cj_zpowers, commW_cj_top, cenW_mp, ← cj_inf, cenW_commW_inf_std]

theorem cenW_commW_inf_le_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    cenW (commW orth (Subgroup.zpowers (zc D)) ⊤) ⊓ D ≤ That D :=
  (cenW_commW_inf_eq hD).le

theorem zc_mem_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) : zc D ∈ That D := by
  obtain ⟨g, rfl, hT, hz, -⟩ := std_data hD
  rw [hT, hz]
  exact mem_cj_conj.mpr zStd_mem_S5That

theorem commW_That_le {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    commW orth (That D) ⊤ ≤ commW orth (Subgroup.zpowers (zc D)) ⊤ := by
  obtain ⟨g, rfl, hT, hz, -⟩ := std_data hD
  rw [hT, hz, ← cj_zpowers, commW_cj_top, commW_cj_top]
  exact Subgroup.map_mono commW_That_std_le

theorem commW_That_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    commW orth (That D) ⊤ = commW orth (Subgroup.zpowers (zc D)) ⊤ := by
  refine le_antisymm (commW_That_le hD) (commW_mono_left' ?_ _)
  exact (Subgroup.zpowers_le).mpr (zc_mem_That hD)

theorem commW_le_of_le_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {A : Subgroup (Perm (Fin 5))} (hA : A ≤ That D) :
    commW orth A ⊤ ≤ commW orth (Subgroup.zpowers (zc D)) ⊤ :=
  (commW_mono_left' hA _).trans (commW_That_le hD)

theorem exists_ne_vp : ∀ g : Perm (Fin 5), g ≠ 1 → ∀ p : Fin 5,
    ∃ w ∈ commF g, w ≠ 1 ∧ w ≠ vp p := by
  unfold commF; decide +kernel

theorem not_commW_le_vp {g : Perm (Fin 5)} (hg : g ≠ 1) (p : Fin 5) :
    ¬ commW orth (Subgroup.zpowers g) ⊤ ≤ Subgroup.zpowers (vp p) := by
  intro h
  obtain ⟨w, hw, h1, h2⟩ := exists_ne_vp g hg p
  have := h ((mem_commW_zpowers_iff g w).mpr hw)
  rw [mem_zpowers_iff_of_mul_self (vp_mul_self p)] at this
  rcases this with h3 | h3
  · exact h1 h3
  · exact h2 h3

theorem std_That_cases : ∀ g : Perm (Fin 5), g ∈ S5ThatF →
    g = 1 ∨ g = zStd ∨ (g ≠ 1 ∧ g ^ 2 = 1 ∧ Perm.sign g ≠ 1) := by
  unfold zStd; decide +kernel

theorem That_cases {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {g : Perm (Fin 5)}
    (hg : g ∈ That D) : g = 1 ∨ g = zc D ∨ g.IsSwap := by
  obtain ⟨g0, rfl, hT, hz, -⟩ := std_data hD
  rw [hT] at hg
  have h1 := std_That_cases _ ((mem_S5That_iff _).mp (mem_cj.mp hg))
  rw [hz]
  rcases h1 with h | h | h
  · left
    have : g = g0 * (g0⁻¹ * g * g0) * g0⁻¹ := by group
    rw [this, h]; group
  · right; left
    have : g = g0 * (g0⁻¹ * g * g0) * g0⁻¹ := by group
    rw [this, h]
  · right; right
    rw [← isSwap_iff] at h
    have := (isSwap_conj g0).mpr h
    simpa [mul_assoc] using this

theorem card_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) : Nat.card (That D) = 4 := by
  obtain ⟨g, rfl, hT, -, -⟩ := std_data hD
  rw [hT, card_cj]
  have h : S5ThatF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

theorem card_commW_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (commW orth (That D) ⊤) = 4 := by
  obtain ⟨g, rfl, hT, hz, -⟩ := std_data hD
  rw [commW_That_eq hD, hz, ← cj_zpowers, commW_cj_top, card_mp]
  exact card_commW_double (a := 0) (b := 2) (c := 1) (d := 3) (p := 4) (by decide)

theorem index_fixW_That {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    (fixW orth (That D)).index = 4 := by
  obtain ⟨g, rfl, hT, -, -⟩ := std_data hD
  rw [hT, fixW_cj]
  have h := (profile_orth.2.2.1)
  simp only [profile, Prod.mk.injEq] at h
  have h2 := Subgroup.card_mul_index (mp g (fixW orth S5That))
  rw [card_mp, h.2.1, card_orth] at h2
  omega

end CFSG.Quasithin.F53.Stellmacher.S35.At
