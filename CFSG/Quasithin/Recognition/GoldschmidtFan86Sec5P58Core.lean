module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58X1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58X3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P58

theorem cases6 {r l i j : ℤ} (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) (h : r + i = l + j)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hl1 : 1 ≤ l) (hl2 : l ≤ 2) :
    (r = 1 ∧ l = 1 ∧ i = 0 ∧ j = 0) ∨ (r = 1 ∧ l = 2 ∧ i = 1 ∧ j = 0) ∨
      (r = 2 ∧ l = 1 ∧ i = 0 ∧ j = 1) ∨ (r = 2 ∧ l = 2 ∧ i = 1 ∧ j = 1) ∨
      (r = 1 ∧ l = 1 ∧ i = 1 ∧ j = 1) ∨ (r = 2 ∧ l = 2 ∧ i = 0 ∧ j = 0) := by
  have hr : r = 1 ∨ r = 2 := by omega
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hr with rfl | rfl <;>
    rcases hl with rfl | rfl <;> omega

theorem fan58_core (F : FanTree Γ G) (h53a : Fan53a F) (h53b : Fan53b F) (h54 : Fan54 F)
    (h51a : Fan51a F) (h40 : Fan40 F) (ℓ : Line Γ) {z z' : G}
    {a b tL tR a' b' tL' tR' i j : ℤ} (hz : z ∈ ℓ.ZZ) (hz' : z' ∈ ℓ.ZZ)
    (hd : ℓ.IsCoreFix z a b tL tR) (hd' : ℓ.IsCoreFix z' a' b' tL' tR')
    (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) (h1 : tR = a' - i) (h2 : tL' = b + j)
    (hr : tR - b ≤ 2) (hl : a' - tL' ≤ 2) :
    ((tR - b = 1 ∧ a' - tL' = 1) ∨ (i = 0 ∧ j = 0)) ∧
      ¬ ((tR - b = 1 ∧ a' - tL' = 1) ∧ (i = 0 ∧ j = 0)) := by
  have hr1 : 1 ≤ tR - b := (h53a h40 ℓ z a b tL tR hz hd).1
  have hl1' : 1 ≤ a' - tL' := (h53a h40 ℓ z' a' b' tL' tR' hz' hd').2.1
  have hcases := P58.cases6 hi hj (by omega) hr1 hr hl1' hl
  have hr3 : valence Γ (ℓ.vert tR) ≠ 3 → 2 ≤ tR - b := (h53a h40 ℓ z a b tL tR hz hd).2.2.1
  have hl3' : valence Γ (ℓ.vert tL') ≠ 3 → 2 ≤ a' - tL' :=
    (h53a h40 ℓ z' a' b' tL' tR' hz' hd').2.2.2
  have e1 := P55.fix_tL_le hd
  have e2 := P55.fix_a_lt hd
  have e3 := P55.fix_le_tR hd
  have e4 := P55.fix_tL_le hd'
  have e5 := P55.fix_a_lt hd'
  have e6 := P55.fix_le_tR hd'
  have hZ : z ∈ ℓ.Zc := P55.zz_le_zc hz
  have hZ' : z' ∈ ℓ.Zc := P55.zz_le_zc hz'
  have hcC : ℓ.IsCoreC z a b := h53b h40 ℓ z a b hz hd.core
  have hcC' : ℓ.IsCoreC z' a' b' := h53b h40 ℓ z' a' b' hz' hd'.core
  have hz2 : z * z = 1 := hz.1
  have hz'2 : z' * z' = 1 := hz'.1
  rcases hcases with hA | hX1 | hX2 | hX3 | hB | hP
  ·
    exfalso
    obtain ⟨c1, c2, c3, c4⟩ := hA
    have h3 : valence Γ (ℓ.vert tR) = 3 := by
      by_contra hne
      have := hr3 hne
      omega
    have h3' : valence Γ (ℓ.vert tL') = 3 := by
      by_contra hne
      have := hl3' hne
      omega
    have hadj : Γ.Adj (ℓ.vert tL') (ℓ.vert tR) := P58.adj' ℓ (by omega)
    exact F.alternating _ _ hadj (h3'.trans h3.symm)
  ·
    exfalso
    obtain ⟨c1, c2, c3, c4⟩ := hX1
    have hv3 : valence Γ (ℓ.vert (b + 1)) = 3 := by
      by_contra hne
      have := hr3 (by rwa [show tR = b + 1 by omega])
      omega
    have hp₀p : Γ.Adj (ℓ.vert (b - 1)) (ℓ.vert b) := P58.adj' ℓ (by ring)
    have hpv : Γ.Adj (ℓ.vert b) (ℓ.vert (b + 1)) := P58.adj' ℓ rfl
    have hvq : Γ.Adj (ℓ.vert (b + 1)) (ℓ.vert (b + 2)) := P58.adj' ℓ (by ring)
    have hqq₂ : Γ.Adj (ℓ.vert (b + 2)) (ℓ.vert (b + 3)) := P58.adj' ℓ (by ring)
    exact P58.x1abs F h40 hp₀p hpv hvq hqq₂ (P58.nb' ℓ (by ring)) (P58.nb' ℓ rfl)
      (P58.nb' ℓ (by ring)) hv3 hz2 hz'2
      ((hd.fix (b - 1)).2 ⟨by omega, by omega⟩) ((hd.fix b).2 ⟨by omega, by omega⟩)
      ((hd.fix (b + 1)).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hd.fix (b + 2)).1 h; omega)
      (P58.central_last hd rfl rfl)
      ((hd'.fix b).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 1)).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hd'.fix (b - 1)).1 h; omega)
      (P58.central_first hd' (by omega) (by omega))
      (P58.f54_left h54 h40 hZ' hcC' (by omega) (by omega))
  ·
    exfalso
    obtain ⟨c1, c2, c3, c4⟩ := hX2
    have hv3 : valence Γ (ℓ.vert (b + 1)) = 3 := by
      by_contra hne
      have := hl3' (by rwa [show tL' = b + 1 by omega])
      omega
    have hp₀p : Γ.Adj (ℓ.vert (b + 3)) (ℓ.vert (b + 2)) := (P58.adj' ℓ (by ring)).symm
    have hpv : Γ.Adj (ℓ.vert (b + 2)) (ℓ.vert (b + 1)) := (P58.adj' ℓ (by ring)).symm
    have hvq : Γ.Adj (ℓ.vert (b + 1)) (ℓ.vert b) := (P58.adj' ℓ rfl).symm
    have hqq₂ : Γ.Adj (ℓ.vert b) (ℓ.vert (b - 1)) := ℓ.adj_pred b
    exact P58.x1abs F h40 hp₀p hpv hvq hqq₂ (P58.nb' ℓ (by ring)).symm (P58.nb' ℓ rfl).symm
      (ℓ.vert_pred_ne_succ b).symm hv3 hz'2 hz2
      ((hd'.fix (b + 3)).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 2)).2 ⟨by omega, by omega⟩)
      ((hd'.fix (b + 1)).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hd'.fix b).1 h; omega)
      (fun h h1 h2 => P58.central_first hd' (i := b + 2) (j := b + 3) (by omega) (by omega) h h2 h1)
      ((hd.fix (b + 2)).2 ⟨by omega, by omega⟩) ((hd.fix (b + 1)).2 ⟨by omega, by omega⟩)
      (fun h => by have := (hd.fix (b + 3)).1 h; omega)
      (fun h h1 h2 => P58.central_last hd (i := b - 1) (j := b) rfl rfl h h2 h1)
      (P58.f54_right h54 h40 hZ hcC (i := b) (j := b - 1) rfl rfl)
  ·
    exfalso
    obtain ⟨c1, c2, c3, c4⟩ := hX3
    have hvv : valence Γ (ℓ.vert (b + 1)) ≠ valence Γ (ℓ.vert (b + 2)) :=
      F.alternating _ _ (P58.adj' ℓ (by ring))
    have hv35 : valence Γ (ℓ.vert (b + 1)) = 3 ∨ valence Γ (ℓ.vert (b + 1)) = 5 := F.valence _
    have hv35' : valence Γ (ℓ.vert (b + 2)) = 3 ∨ valence Γ (ℓ.vert (b + 2)) = 5 := F.valence _
    have hone : valence Γ (ℓ.vert (b + 1)) = 3 ∨ valence Γ (ℓ.vert (b + 2)) = 3 := by omega
    rcases hone with hv3 | hv3
    ·
      have hval3 : valence Γ (ℓ.vert (b + 3)) = 3 := by
        have := ℓ.valence_add_two F (b + 1)
        rw [show b + 1 + 2 = b + 3 by ring] at this
        omega
      obtain ⟨u, hu1, hu2, huv, huq, hc1, hc2⟩ := P58.x3abs F h40
        (P58.adj' ℓ (i := b - 1) (j := b) (by ring)) (P58.adj' ℓ (i := b) (j := b + 1) rfl)
        (P58.adj' ℓ (i := b + 1) (j := b + 2) (by ring))
        (P58.adj' ℓ (i := b + 2) (j := b + 3) (by ring))
        (P58.adj' ℓ (i := b + 3) (j := b + 4) (by ring))
        (P58.nb' ℓ (by ring)) (P58.nb' ℓ rfl) (P58.nb' ℓ (by ring)) (P58.nb' ℓ (by ring)) hv3
        hz2 hz'2
        ((hd.fix (b - 1)).2 ⟨by omega, by omega⟩) ((hd.fix b).2 ⟨by omega, by omega⟩)
        ((hd.fix (b + 1)).2 ⟨by omega, by omega⟩) ((hd.fix (b + 2)).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hd.fix (b + 3)).1 h; omega)
        (P58.central_last hd rfl rfl) (P58.f54_right h54 h40 hZ hcC rfl rfl)
        ((hd'.fix (b + 1)).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 2)).2 ⟨by omega, by omega⟩)
        ((hd'.fix (b + 3)).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 4)).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hd'.fix b).1 h; omega)
        (P58.central_first hd' (i := b + 3) (j := b + 4) (by omega) (by omega))
      refine P58.final3 F h40 h51a ℓ b hu1 (fun g hg => ?_) (fun g hg => ?_) huv huq
      · exact hc1 g (P58.edgeCirc_fix' hg rfl).1 (P58.edgeCirc_fix' hg rfl).2
          (P57.edgeCirc_cond F ℓ hg).1
      · have hf := P58.edgeCirc_fix' (i := b + 2) (j := b + 3) hg (by ring)
        exact hc2 g hf.1 hf.2 hval3
    ·
      have hval0 : valence Γ (ℓ.vert b) = 3 := by
        have := ℓ.valence_add_two F b
        omega
      obtain ⟨u, hu1, hu2, huv, huq, hc1, hc2⟩ := P58.x3abs F h40
        (P58.adj' ℓ (i := b + 3) (j := b + 4) (by ring)).symm
        (P58.adj' ℓ (i := b + 2) (j := b + 3) (by ring)).symm
        (P58.adj' ℓ (i := b + 1) (j := b + 2) (by ring)).symm
        (P58.adj' ℓ (i := b) (j := b + 1) rfl).symm (ℓ.adj_pred b)
        (P58.nb' ℓ (i := b + 2) (j := b + 4) (by ring)).symm
        (P58.nb' ℓ (i := b + 1) (j := b + 3) (by ring)).symm
        (P58.nb' ℓ (i := b) (j := b + 2) rfl).symm (ℓ.vert_pred_ne_succ b).symm hv3 hz'2 hz2
        ((hd'.fix (b + 4)).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 3)).2 ⟨by omega, by omega⟩)
        ((hd'.fix (b + 2)).2 ⟨by omega, by omega⟩) ((hd'.fix (b + 1)).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hd'.fix b).1 h; omega)
        (fun h h1 h2 => P58.central_first hd' (i := b + 3) (j := b + 4) (by omega) (by omega)
          h h2 h1)
        (P58.f54_left h54 h40 hZ' hcC' (i := b + 3) (j := b + 4) (by omega) (by omega))
        ((hd.fix (b + 2)).2 ⟨by omega, by omega⟩) ((hd.fix (b + 1)).2 ⟨by omega, by omega⟩)
        ((hd.fix b).2 ⟨by omega, by omega⟩) ((hd.fix (b - 1)).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hd.fix (b + 3)).1 h; omega)
        (fun h h1 h2 => P58.central_last hd (i := b - 1) (j := b) rfl rfl h h2 h1)
      refine P58.final3 F h40 h51a ℓ b hu1 (fun g hg => ?_) (fun g hg => ?_) huq huv
      · exact hc2 g (P58.edgeCirc_fix' hg rfl).2 (P58.edgeCirc_fix' hg rfl).1 hval0
      · have hf := P58.edgeCirc_fix' (i := b + 2) (j := b + 3) hg (by ring)
        have hcond := (P57.edgeCirc_cond F ℓ hg).2
        rw [show b + 2 + 1 = b + 3 by ring] at hcond
        exact hc1 g hf.2 hf.1 hcond
  · omega
  · omega

end P58

end CFSG.Quasithin.Fan86
