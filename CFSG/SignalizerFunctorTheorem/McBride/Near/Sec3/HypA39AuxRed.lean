module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxQuot

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ]

structure L39 (p : ℕ) (H A D D₁ D₂ E : Subgroup Γ) : Prop where
  h15 : HypA15 p H A D D₁ D₂
  hEA : E ≤ A
  hE : Nat.card E = p ^ 2
  h6 : ∀ e ∈ E, e ≠ 1 → HypA6 (H ⊓ Subgroup.centralizer {e}) A D D₁ D₂
  h5 : p = 3 → ∀ x ∈ D₁, ∃ k : ℕ, x ^ (5 ^ k) ∈ D₂
  restrict : ∀ H' : Subgroup Γ, H' ≤ H → D ≤ H' → Admits (D ⊔ A) H' → H' ⊔ A ≠ H ⊔ A →
    HypA6 H' A D D₁ D₂
  quot : ∀ M : Subgroup Γ, M ≤ H → Admits (H ⊔ A) M → M ≠ ⊥ → M ⊓ D ≤ D₂ →
    HypA6 (AChief.qimg M H) (AChief.qimg M A) (AChief.qimg M D) (AChief.qimg M D₁)
      (AChief.qimg M D₂)

section Reduction

variable {p : ℕ} {H A D D₁ D₂ E : Subgroup Γ}

theorem L39.restrict_to [Finite Γ] (c : L39 p H A D D₁ D₂ E) {H' : Subgroup Γ} (hH' : H' ≤ H)
    (hD : D ≤ H') (hadm : Admits (D ⊔ A) H') (heq : H' ⊔ A = H ⊔ A) :
    L39 p H' A D D₁ D₂ E where
  h15 := c.h15.restrict hH' hD hadm
  hEA := c.hEA
  hE := c.hE
  h6 e he he1 := (c.h6 e he he1).mono (inf_le_inf_right _ hH')
  h5 := c.h5
  restrict H'' hH'' hD' hadm' hne :=
    c.restrict H'' (hH''.trans hH') hD' hadm' (by rwa [heq] at hne)
  quot M hM hMadm hM0 hMD := by
    rw [heq] at hMadm
    exact (c.quot M (hM.trans hH') hMadm hM0 hMD).mono (SolQuot.qimg_mono hH')

theorem exists_triple_of_not_hypA6 {H A D D₁ D₂ : Subgroup Γ} (h : ¬ HypA6 H A D D₁ D₂) :
    ∃ N L R : Subgroup Γ, N ≤ H ∧ L ≤ H ∧ R ≤ H ∧ Admits (D ⊔ A) N ∧ Admits (D ⊔ A) L ∧
      Admits (D ⊔ A) R ∧ L ≤ R ∧ IsChiefFactorOf (R ⊔ D ⊔ A) L N ∧
      A ⊔ R ≤ secCenIn (R ⊔ D ⊔ A) L N ∧ R ⊓ D = D₁ ∧ D ⊓ N ≤ D₂ ∧
      IsDirectProductMod N (D₁ ⊔ N) (D₂ ⊔ N) L ∧ ¬ HasB A D D₁ D₂ R := by
  by_contra hcon
  apply h
  intro N L R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  by_contra hB
  exact hcon ⟨N, L, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hB⟩

theorem comm_of_D₁_eq {p : ℕ} {H A D D₁ D₂ L : Subgroup Γ} (h : HypA15 p H A D D₁ D₂)
    (hD₁ : D₁ = D₂ ⊔ L) (hD₂L : D₂ ⊓ L = ⊥) (hLG : Admits (H ⊔ A) L) (hLH : L ≤ H) :
    ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  intro x hx y hy
  have hLD₁ : L ≤ D₁ := by
    rw [hD₁]
    exact le_sup_right
  have hxD₁ : x ∈ secCenIn D D₁ D₂ := by
    rw [h.a4c]
    exact hLD₁ hx
  have hcomm := (McBride.mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp hxD₁).2).2.2
  have h1 : ⁅x, y⁆ ∈ D₂ := hcomm y (hLD₁ hy)
  have hyG : y ∈ H ⊔ A := Subgroup.mem_sup_left (hLH hy)
  have h2 : ⁅x, y⁆ ∈ L := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hx (by simpa [mul_assoc] using hLG.conj_mem hyG (inv_mem hx))
  have h3 : ⁅x, y⁆ ∈ D₂ ⊓ L := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [hD₂L, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem centralizer_inf_D_le {p : ℕ} {H A D D₁ D₂ L : Subgroup Γ} (h : HypA15 p H A D D₁ D₂)
    (hD₁ : D₁ = D₂ ⊔ L) (hLD : L ≤ D) : D ⊓ Subgroup.centralizer (L : Set Γ) ≤ D₁ := by
  intro x hx
  obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.mp hx
  have hmem : x ∈ secCenIn D D₁ D₂ := by
    refine Subgroup.mem_inf.mpr ⟨hxD, McBride.mem_sectionCentralizer_iff.mpr
      ⟨h.a4_chief.1.2 hxD, h.a4_chief.2.1.2 hxD, fun y hy => ?_⟩⟩
    rw [hD₁] at hy
    have hLN : L ≤ Subgroup.normalizer (D₂ : Set Γ) := fun l hl => h.a4_chief.1.2 (hLD hl)
    obtain ⟨d, hd, l, hl, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hLN).mp hy
    have hxl : x * l * x⁻¹ = l := by
      have := Subgroup.mem_centralizer_iff.mp hxC l hl
      rw [this.symm, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : x * d * x⁻¹ ∈ D₂ := (Subgroup.mem_normalizer_iff.mp (h.a4_chief.1.2 hxD) d).mp hd
    have h2 : ⁅x, d * l⁆ = (x * d * x⁻¹) * d⁻¹ := by
      calc ⁅x, d * l⁆ = (x * d * x⁻¹) * (x * l * x⁻¹) * l⁻¹ * d⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = (x * d * x⁻¹) * l * l⁻¹ * d⁻¹ := by rw [hxl]
        _ = (x * d * x⁻¹) * d⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem hd)
  rw [h.a4c] at hmem
  exact hmem

structure Red (p : ℕ) (H A D D₁ D₂ E L R : Subgroup Γ) : Prop extends L39 p H A D D₁ D₂ E where
  hR : R = H ⊓ Subgroup.centralizer (L : Set Γ)
  hHR : H = R ⊔ D
  hL0 : L ≠ ⊥
  hLG : Admits (H ⊔ A) L
  hLmin : ∀ M : Subgroup Γ, M ≤ L → Admits (H ⊔ A) M → M = ⊥ ∨ M = L
  hD₁ : D₁ = D₂ ⊔ L
  hD₂L : D₂ ⊓ L = ⊥
  hD₂c : ∀ d ∈ D₂, ∀ l ∈ L, d * l = l * d
  hRD : R ⊓ D = D₁
  noB : ¬ HasB A D D₁ D₂ R

end Reduction

section RedBasic

variable {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

namespace Red

theorem D_le (c : Red p H A D D₁ D₂ E L R) : D ≤ H := c.h15.D_le

theorem D₁_le_D (c : Red p H A D D₁ D₂ E L R) : D₁ ≤ D := c.h15.D₁_le

theorem D₂_le_D₁ (c : Red p H A D D₁ D₂ E L R) : D₂ ≤ D₁ := c.h15.D₂_lt.le

theorem D₂_le_D (c : Red p H A D D₁ D₂ E L R) : D₂ ≤ D := c.h15.D₂_le

theorem L_le_D₁ (c : Red p H A D D₁ D₂ E L R) : L ≤ D₁ := by
  rw [c.hD₁]
  exact le_sup_right

theorem L_le_D (c : Red p H A D D₁ D₂ E L R) : L ≤ D := c.L_le_D₁.trans c.D₁_le_D

theorem D₁_le_R (c : Red p H A D D₁ D₂ E L R) : D₁ ≤ R := by
  rw [← c.hRD]
  exact inf_le_left

theorem L_le_R (c : Red p H A D D₁ D₂ E L R) : L ≤ R := c.L_le_D₁.trans c.D₁_le_R

theorem D₂_le_R (c : Red p H A D D₁ D₂ E L R) : D₂ ≤ R := c.D₂_le_D₁.trans c.D₁_le_R

theorem R_le_H (c : Red p H A D D₁ D₂ E L R) : R ≤ H := by
  rw [c.hR]
  exact inf_le_left

theorem L_le_H (c : Red p H A D D₁ D₂ E L R) : L ≤ H := c.L_le_R.trans c.R_le_H

theorem G_eq (c : Red p H A D D₁ D₂ E L R) : R ⊔ D ⊔ A = H ⊔ A := by
  rw [← c.hHR]

theorem DA_le_G (c : Red p H A D D₁ D₂ E L R) : D ⊔ A ≤ H ⊔ A :=
  sup_le (c.D_le.trans le_sup_left) le_sup_right

theorem admits_H (c : Red p H A D D₁ D₂ E L R) : Admits (D ⊔ A) H :=
  sup_le (c.D_le.trans Subgroup.le_normalizer) c.h15.a1_admits

theorem admits_H_G (c : Red p H A D D₁ D₂ E L R) : Admits (H ⊔ A) H :=
  sup_le Subgroup.le_normalizer c.h15.a1_admits

theorem admits_L (c : Red p H A D D₁ D₂ E L R) : Admits (D ⊔ A) L := c.DA_le_G.trans c.hLG

theorem admits_R_G (c : Red p H A D D₁ D₂ E L R) : Admits (H ⊔ A) R := by
  rw [c.hR]
  exact c.admits_H_G.inf (c.hLG.trans (HypAAux.normalizer_le_normalizer_centralizer L))

theorem admits_R (c : Red p H A D D₁ D₂ E L R) : Admits (D ⊔ A) R := c.DA_le_G.trans c.admits_R_G

theorem admits_D (c : Red p H A D D₁ D₂ E L R) : Admits (D ⊔ A) D := c.h15.admits_D

theorem R_cen (c : Red p H A D D₁ D₂ E L R) : ∀ x ∈ R, ∀ y ∈ L, x * y = y * x := by
  intro x hx y hy
  have : x ∈ Subgroup.centralizer (L : Set Γ) := (Subgroup.mem_inf.mp (c.hR ▸ hx)).2
  exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

theorem A_cen (c : Red p H A D D₁ D₂ E L R) : ∀ a ∈ A, ∀ y ∈ L, a * y = y * a := by
  intro a ha y hy
  exact Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer (c.L_le_D hy)) a ha

theorem L_comm (c : Red p H A D D₁ D₂ E L R) : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x :=
  comm_of_D₁_eq c.h15 c.hD₁ c.hD₂L c.hLG c.L_le_H


end Red

end RedBasic

section ExistsRed

theorem exists_red [Finite Γ] {p : ℕ} {H A D D₁ D₂ E : Subgroup Γ} (c : L39 p H A D D₁ D₂ E)
    (h : ¬ HypA6 H A D D₁ D₂) : ∃ H' L R : Subgroup Γ, Red p H' A D D₁ D₂ E L R := by
  obtain ⟨N, L, R, hNH, hLH, hRH, hNadm, hLadm, hRadm, hLR, hchief, hcen, hRD, hND, hdir, hnoB⟩ :=
    exists_triple_of_not_hypA6 h
  have hNL : N ≤ L := hchief.2.2.1.le
  have hNR : N ≤ R := hNL.trans hLR
  have hDH : D ≤ H := c.h15.D_le
  have hD₂D : D₂ ≤ D := c.h15.D₂_le
  have hD₁D : D₁ ≤ D := c.h15.D₁_le
  have hD₂D₁ : D₂ ≤ D₁ := c.h15.D₂_lt.le
  have hRDadm : Admits (D ⊔ A) (R ⊔ D) := hRadm.sup c.h15.admits_D
  have hRDH : R ⊔ D ≤ H := sup_le hRH hDH
  have hG : R ⊔ D ⊔ A = H ⊔ A := by
    by_contra hne
    have h6 := c.restrict (R ⊔ D) hRDH le_sup_right hRDadm hne
    exact hnoB (h6 N L R (hNR.trans le_sup_left) (hLR.trans le_sup_left) le_sup_left hNadm hLadm
      hRadm hLR hchief hcen hRD hND hdir)
  have c' := c.restrict_to hRDH le_sup_right hRDadm hG
  have hN0 : N = ⊥ := by
    by_contra hN0
    have h6 := c'.quot N (hNR.trans le_sup_left) hchief.1.2 hN0 (by rw [inf_comm]; exact hND)
    exact hnoB (hasB_of_quot c'.h15 hchief.1.2 h6 le_rfl hLR le_sup_left hNadm hLadm hRadm hchief
      hcen hRD hND hdir)
  subst hN0
  have hRcen : ∀ x ∈ R, ∀ y ∈ L, x * y = y * x := fun x hx y hy => by
    have := (McBride.mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp
      (hcen (show x ∈ A ⊔ R from Subgroup.mem_sup_right hx))).2).2.2 y hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
  have hRC : R ≤ Subgroup.centralizer (L : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hRcen x hx y hy).symm
  have hD₁eq : D₁ = D₂ ⊔ L := by
    have := hdir.2.2.1
    rwa [sup_bot_eq, sup_bot_eq, eq_comm] at this
  have hD₂L : D₂ ⊓ L = ⊥ := by
    have := hdir.2.2.2.1
    rwa [sup_bot_eq] at this
  have hD₂c : ∀ d ∈ D₂, ∀ l ∈ L, d * l = l * d := fun d hd l hl => by
    have := hdir.2.2.2.2 (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hd) hl)
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
  have hLG : Admits (H ⊔ A) L := by
    rw [← hG]
    exact hchief.2.1.2
  have hLD : L ≤ D := by
    have : L ≤ D₁ := by
      rw [hD₁eq]
      exact le_sup_right
    exact this.trans hD₁D
  have hD₁R : D₁ ≤ R := by
    rw [← hRD]
    exact inf_le_left
  have hLcomm := comm_of_D₁_eq c.h15 hD₁eq hD₂L hLG hLH
  refine ⟨R ⊔ D, L, (R ⊔ D) ⊓ Subgroup.centralizer (L : Set Γ), ?_⟩
  have hRR₂ : R ≤ (R ⊔ D) ⊓ Subgroup.centralizer (L : Set Γ) := le_inf le_sup_left hRC
  exact
    { toL39 := c'
      hR := rfl
      hHR := le_antisymm (sup_le_sup_right hRR₂ D) (sup_le inf_le_left le_sup_right)
      hL0 := bot_lt_iff_ne_bot.mp hchief.2.2.1
      hLG := by
        rw [hG] at *
        exact hLG
      hLmin := fun M hML hM => hchief.2.2.2 M ⟨hML.trans (hLR.trans (le_sup_left.trans
        le_sup_left)), hM⟩ bot_le hML
      hD₁ := hD₁eq
      hD₂L := hD₂L
      hD₂c := hD₂c
      hRD := by
        refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (hD₁D.trans le_sup_right) ?_) hD₁D)
        · have hx' := Subgroup.mem_inf.mp hx
          have hx1 := Subgroup.mem_inf.mp hx'.1
          exact centralizer_inf_D_le c.h15 hD₁eq hLD (Subgroup.mem_inf.mpr ⟨hx'.2, hx1.2⟩)
        · intro y hy
          rw [hD₁eq] at hy
          have hLN : L ≤ Subgroup.normalizer (D₂ : Set Γ) := fun l hl =>
            c.h15.a4_chief.1.2 (hLD hl)
          obtain ⟨d, hd, l', hl', rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hLN).mp hy
          refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
          calc l * (d * l') = (l * d) * l' := by rw [mul_assoc]
            _ = (d * l) * l' := by rw [hD₂c d hd l hl]
            _ = d * (l * l') := by rw [mul_assoc]
            _ = d * (l' * l) := by rw [hLcomm l hl l' hl']
            _ = d * l' * l := by rw [mul_assoc]
      noB := fun hB => hnoB (hB.of_le hRR₂ hD₁R hD₂D₁ hRadm hD₁D) }

end ExistsRed

end CFSG.SignalizerFunctorTheorem.McBride.Near
