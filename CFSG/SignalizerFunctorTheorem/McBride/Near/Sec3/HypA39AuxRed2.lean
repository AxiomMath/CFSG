module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxRed

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ]

theorem mem_normalizer_bot (g : Γ) : g ∈ Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem commutator_mul_mem_of_normal {M : Subgroup Γ} {p q m m' : Γ}
    (hp : p ∈ Subgroup.normalizer (M : Set Γ)) (hq : q ∈ Subgroup.normalizer (M : Set Γ))
    (hm : m ∈ M) (hm' : m' ∈ M) (hpq : ⁅p, q⁆ ∈ M) : ⁅p * m, q * m'⁆ ∈ M := by
  have hpq' : p * q ∈ Subgroup.normalizer (M : Set Γ) := mul_mem hp hq
  have ha : q⁻¹ * m * q ∈ M := by
    have := (Subgroup.mem_normalizer_iff''.mp hq m).mp hm
    exact this
  have hb : p⁻¹ * m' * p ∈ M := (Subgroup.mem_normalizer_iff''.mp hp m').mp hm'
  set u : Γ := (q⁻¹ * m * q) * m' * m⁻¹ * (p⁻¹ * m' * p)⁻¹ with hu
  have huM : u ∈ M := mul_mem (mul_mem (mul_mem ha hm') (inv_mem hm)) (inv_mem hb)
  have hid : ⁅p * m, q * m'⁆ = (p * q) * u * (p * q)⁻¹ * ⁅p, q⁆ := by
    rw [hu]
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp hpq' u).mp huM |> fun h => by
    simpa [mul_assoc] using h) hpq

variable {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

namespace Red

theorem hasB_of_hypA6 (c : Red p H A D D₁ D₂ E L R) {H' R' : Subgroup Γ}
    (h6 : HypA6 H' A D D₁ D₂) (hR'H' : R' ≤ H') (hLR' : L ≤ R') (hR'R : R' ≤ R)
    (hadm : Admits (D ⊔ A) R') (hRD' : R' ⊓ D = D₁) : HasB A D D₁ D₂ R' := by
  have hR'cen : ∀ g ∈ R', ∀ x ∈ L, g * x = x * g := fun g hg x hx => c.R_cen g (hR'R hg) x hx
  have hcenAR : A ⊔ R' ≤ Subgroup.centralizer (L : Set Γ) := by
    refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (fun g hg => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    · exact (c.A_cen a ha y hy).symm
    · exact (hR'cen g hg y hy).symm
  have hLadm : Admits (R' ⊔ D ⊔ A) L :=
    sup_le (sup_le (admits_of_centralizes hR'cen) (le_sup_left.trans c.admits_L))
      (le_sup_right.trans c.admits_L)
  refine h6 ⊥ L R' bot_le (hLR'.trans hR'H') hR'H' (admits_bot _) c.admits_L hadm hLR' ?_ ?_
    hRD' (by simp) ?_
  · refine ⟨⟨bot_le, fun g _ => mem_normalizer_bot g⟩,
      ⟨hLR'.trans (le_sup_left.trans le_sup_left), hLadm⟩, bot_lt_iff_ne_bot.mpr c.hL0,
      fun K hK _ hKL => ?_⟩
    have hRK : R ≤ Subgroup.normalizer (K : Set Γ) :=
      admits_of_centralizes (fun g hg x hx => c.R_cen g hg x (hKL hx))
    have hKG : Admits (H ⊔ A) K := by
      rw [← c.G_eq]
      exact sup_le (sup_le hRK ((le_sup_right.trans le_sup_left).trans hK.2))
        (le_sup_right.trans hK.2)
    exact c.hLmin K hKL hKG
  · refine le_inf (sup_le le_sup_right (le_sup_left.trans le_sup_left)) fun x hx => ?_
    have hxC := hcenAR hx
    refine McBride.mem_sectionCentralizer_iff.mpr ⟨mem_normalizer_bot x,
      Subgroup.centralizer_le_normalizer _ hxC, fun y hy => ?_⟩
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hxC y hy).symm)
  · refine ⟨bot_le, bot_le, ?_, ?_, ?_⟩
    · rw [sup_bot_eq, sup_bot_eq, c.hD₁]
    · rw [sup_bot_eq]
      exact c.hD₂L
    · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      rw [sup_bot_eq] at hx
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (c.hD₂c x hx y hy))

theorem not_le_of_normal (c : Red p H A D D₁ D₂ E L R) {M : Subgroup Γ}
    (hMD : M ⊓ D ≤ D₂) : ¬ L ≤ M := by
  intro hLM
  have h1 : L ≤ D₂ := fun x hx => hMD (Subgroup.mem_inf.mpr ⟨hLM hx, c.L_le_D hx⟩)
  have h2 : L ≤ D₂ ⊓ L := le_inf h1 le_rfl
  rw [c.hD₂L] at h2
  exact c.hL0 (le_bot_iff.mp h2)

theorem inf_L_eq_bot (c : Red p H A D D₁ D₂ E L R) {M : Subgroup Γ} (hM : Admits (H ⊔ A) M)
    (hMD : M ⊓ D ≤ D₂) : M ⊓ L = ⊥ := by
  rcases c.hLmin (M ⊓ L) inf_le_right (hM.inf c.hLG) with h | h
  · exact h
  · exact absurd (inf_eq_right.mp h) (c.not_le_of_normal hMD)

theorem le_R_of_normal (c : Red p H A D D₁ D₂ E L R) {M : Subgroup Γ} (hMH : M ≤ H)
    (hM : Admits (H ⊔ A) M) (hMD : M ⊓ D ≤ D₂) : M ≤ R := by
  have hML := c.inf_L_eq_bot hM hMD
  rw [c.hR]
  refine le_inf hMH fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hyG : y ∈ H ⊔ A := Subgroup.mem_sup_left (c.L_le_H hy)
  have hxG : x ∈ H ⊔ A := Subgroup.mem_sup_left (hMH hx)
  have h1 : ⁅x, y⁆ ∈ M := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hx (by simpa [mul_assoc] using hM.conj_mem hyG (inv_mem hx))
  have h2 : ⁅x, y⁆ ∈ L := by
    rw [commutatorElement_def]
    exact mul_mem (c.hLG.conj_mem hxG hy) (inv_mem hy)
  have h3 : ⁅x, y⁆ ∈ M ⊓ L := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [hML, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

theorem eq_bot_of_normal [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {M : Subgroup Γ}
    (hMH : M ≤ H) (hM : Admits (H ⊔ A) M) (hMD : M ⊓ D ≤ D₂) : M = ⊥ := by
  by_contra hM0
  have h6 := c.quot M hMH hM hM0 hMD
  have hMR := c.le_R_of_normal hMH hM hMD
  have hLM := c.not_le_of_normal hMD
  have hMDA : Admits (D ⊔ A) M := hM.mono_left c.DA_le_G
  have hLMadm : Admits (D ⊔ A) (L ⊔ M) := c.admits_L.sup hMDA
  have hLG' : Admits (H ⊔ A) (L ⊔ M) := c.hLG.sup hM
  have hMG : Admits (R ⊔ D ⊔ A) M := by
    rw [c.G_eq]
    exact hM
  have hLMG : Admits (R ⊔ D ⊔ A) (L ⊔ M) := by
    rw [c.G_eq]
    exact hLG'
  have hcenAR : A ⊔ R ≤ Subgroup.centralizer (L : Set Γ) := by
    refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (fun g hg => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    · exact (c.A_cen a ha y hy).symm
    · exact (c.R_cen g hg y hy).symm
  have hMN : M ≤ Subgroup.normalizer (L : Set Γ) := fun m hm => c.hLG (Subgroup.mem_sup_left
    (hMH hm))
  have hLN : L ≤ Subgroup.normalizer (M : Set Γ) := fun l hl => hM (Subgroup.mem_sup_left
    (c.L_le_H hl))
  have hMY : M ≤ R ⊔ D ⊔ A := hMR.trans (le_sup_left.trans le_sup_left)
  have hD₂N : D₂ ≤ Subgroup.normalizer (M : Set Γ) := fun d hd =>
    hM (Subgroup.mem_sup_left (c.D_le (c.D₂_le_D hd)))
  refine c.noB (hasB_of_quot c.h15 hM h6 le_rfl (sup_le c.L_le_R hMR) c.R_le_H hMDA hLMadm
    c.admits_R ?_ ?_ c.hRD (by rw [inf_comm]; exact hMD) ?_)
  ·
    refine ⟨⟨hMY, hMG⟩, ⟨sup_le (c.L_le_R.trans (le_sup_left.trans le_sup_left)) hMY, hLMG⟩,
      lt_of_le_of_ne le_sup_right fun h => hLM (le_sup_left.trans h.symm.le),
      fun K hK hMK hKL => ?_⟩
    have hKG : Admits (H ⊔ A) K := by
      rw [← c.G_eq]
      exact hK.2
    rcases c.hLmin (K ⊓ L) inf_le_right (hKG.inf c.hLG) with h | h
    · left
      have h1 : K ≤ M ⊔ (K ⊓ L) := by
        refine (le_inf le_rfl ?_).trans (inf_sup_le_sup_inf' hMK hLN)
        rwa [sup_comm]
      rw [h, sup_bot_eq] at h1
      exact le_antisymm h1 hMK
    · right
      exact le_antisymm hKL (sup_le (inf_eq_right.mp h) hMK)
  ·
    have hAR : A ⊔ R ≤ R ⊔ D ⊔ A := sup_le le_sup_right (le_sup_left.trans le_sup_left)
    refine le_inf hAR fun x hx => ?_
    have hx' : x ∈ R ⊔ D ⊔ A := hAR hx
    refine McBride.mem_sectionCentralizer_iff.mpr ⟨hMG hx', hLMG hx', fun y hy => ?_⟩
    obtain ⟨l, hl, m, hm, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hMN).mp hy
    have hxl : x * l * x⁻¹ = l := by
      have := Subgroup.mem_centralizer_iff.mp (hcenAR hx) l hl
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    have hxG : x ∈ H ⊔ A := c.G_eq ▸ hx'
    have hl' : l ∈ H ⊔ A := Subgroup.mem_sup_left (c.L_le_H hl)
    have hcomm : ⁅x, m⁆ ∈ M := by
      rw [commutatorElement_def]
      exact mul_mem (hM.conj_mem hxG hm) (inv_mem hm)
    have hid : ⁅x, l * m⁆ = l * ⁅x, m⁆ * l⁻¹ := by
      calc ⁅x, l * m⁆ = (x * l * x⁻¹) * (x * m * x⁻¹ * m⁻¹) * l⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = l * ⁅x, m⁆ * l⁻¹ := by rw [hxl]; rfl
    rw [hid]
    exact hM.conj_mem hl' hcomm |> fun h => by simpa [mul_assoc] using h
  ·
    refine ⟨le_sup_right, le_sup_right, ?_, ?_, ?_⟩
    · rw [sup_sup_sup_comm, sup_idem, c.hD₁]
    · refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨d, hd, m, hm, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hD₂N).mp hx1
      obtain ⟨l, hl, m', hm', hdl⟩ := (mem_sup_iff_mul_of_le_normalizer' hMN).mp hx2
      have hu : d⁻¹ * l = m * m'⁻¹ := by
        calc d⁻¹ * l = d⁻¹ * (l * m') * m'⁻¹ := by group
          _ = d⁻¹ * (d * m) * m'⁻¹ := by rw [← hdl]
          _ = m * m'⁻¹ := by group
      have huM : d⁻¹ * l ∈ M := hu ▸ mul_mem hm (inv_mem hm')
      have huD : d⁻¹ * l ∈ D := mul_mem (inv_mem (c.D₂_le_D hd)) (c.L_le_D hl)
      have hl2 : l ∈ D₂ := by
        have := mul_mem hd (hMD (Subgroup.mem_inf.mpr ⟨huM, huD⟩))
        simpa using this
      have hl1 : l = 1 := by
        have : l ∈ D₂ ⊓ L := Subgroup.mem_inf.mpr ⟨hl2, hl⟩
        rw [c.hD₂L] at this
        exact Subgroup.mem_bot.mp this
      rw [hdl, hl1, one_mul]
      exact hm'
    · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨d, hd, m, hm, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hD₂N).mp hx
      obtain ⟨l, hl, m', hm', rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hLN).mp hy
      refine commutator_mul_mem_of_normal (hD₂N hd) (hLN hl) hm hm' ?_
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (c.hD₂c d hd l hl)]
      exact one_mem _

theorem R_ne_D₁ (c : Red p H A D D₁ D₂ E L R) : R ≠ D₁ := by
  intro h
  have hRD : R ≤ D := h.le.trans c.D₁_le_D
  refine c.noB ⟨D₂, c.D₂_le_R, ?_, inf_eq_left.mpr c.D₂_le_D, ?_⟩
  · exact c.h15.admits_D₂.mono_left (sup_le (sup_le (hRD.trans le_sup_left) le_sup_left)
      le_sup_right)
  · rw [sup_eq_right.mpr c.D₂_le_D₁]
    exact h

theorem hasB_sup (c : Red p H A D D₁ D₂ E L R) {K : Subgroup Γ} (hK : Admits (H ⊔ A) K)
    (hLK : L ≤ K) (hKR : K ≤ R) (hne : K ⊔ D₁ ≠ R) : HasB A D D₁ D₂ (K ⊔ D₁) := by
  have hKH : K ≤ H := hKR.trans c.R_le_H
  have hKDH : K ⊔ D ≤ H := sup_le hKH c.D_le
  have hKDA : Admits (D ⊔ A) K := hK.mono_left c.DA_le_G
  have hadm : Admits (D ⊔ A) (K ⊔ D) := hKDA.sup c.admits_D
  have hDK : D ≤ Subgroup.normalizer (K : Set Γ) := fun d hd =>
    hK (Subgroup.mem_sup_left (c.D_le hd))
  have hD₁K : D₁ ≤ Subgroup.normalizer (K : Set Γ) := fun d hd => hDK (c.D₁_le_D hd)
  have hne' : K ⊔ D ⊔ A ≠ H ⊔ A := by
    intro heq
    have hRKD : R ≤ K ⊔ D := by
      intro x hx
      have hxG : x ∈ K ⊔ D ⊔ A := by
        rw [heq]
        exact Subgroup.mem_sup_left (c.R_le_H hx)
      exact c.h15.inf_sup_le_of_le hKDH (hadm.mono_left le_sup_right)
        (Subgroup.mem_inf.mpr ⟨c.R_le_H hx, hxG⟩)
    have hR : R ≤ K ⊔ D₁ := by
      have h1 : R ≤ R ⊓ (K ⊔ D) := le_inf le_rfl hRKD
      have h2 := inf_sup_le_sup_inf' (S := K) (U := R) (X := D) hKR hDK
      rw [c.hRD] at h2
      exact h1.trans h2
    exact hne (le_antisymm (sup_le hKR c.D₁_le_R) hR)
  have h6 := c.restrict (K ⊔ D) hKDH le_sup_right hadm hne'
  refine c.hasB_of_hypA6 h6 (sup_le_sup_left c.D₁_le_D K) (hLK.trans le_sup_left)
    (sup_le hKR c.D₁_le_R) (hKDA.sup c.h15.admits_D₁) ?_
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right c.D₁_le_D)
  obtain ⟨hx1, hxD⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk, d, hd, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hD₁K).mp hx1
  have hkD : k ∈ D := by
    have := mul_mem hxD (inv_mem (c.D₁_le_D hd))
    simpa using this
  have hkD₁ : k ∈ D₁ := by
    rw [← c.hRD]
    exact Subgroup.mem_inf.mpr ⟨hKR hk, hkD⟩
  exact mul_mem hkD₁ hd

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
