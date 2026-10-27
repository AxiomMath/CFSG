module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs

import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallBasic

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {z : V}
  {H A : Subgroup (V ≃ₗ[ZMod 3] V)}

private def hdRo7A9ExclAux_rho (hh f : Fin 9 → ZMod 3) (d : ZMod 3)
    (hh' f' : Fin 9 → ZMod 3) (d' : ZMod 3) (σ : Equiv.Perm (Fin 9)) :
    (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3 :=
  a9Act hh f d ∘ ((a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹) ∘ a9Act hh f d

private theorem hdRo7A9ExclAux_conj_wit
    (hD : A3LinData 3 9 V θ z H A)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    {hh f : Fin 9 → ZMod 3} {d : ZMod 3} {r : V ≃ₗ[ZMod 3] V}
    (hrH : r ∈ H) (hr : A9Real θ z hh f d r) (hhU : hh ∈ a3Aug 3 9)
    {hh' f' : Fin 9 → ZMod 3} {d' : ZMod 3} {r' : V ≃ₗ[ZMod 3] V}
    (hr'H : r' ∈ H) (hr' : A9Real θ z hh' f' d' r') (hhU' : hh' ∈ a3Aug 3 9)
    (σ : Equiv.Perm (Fin 9)) (i j : Fin 9)
    (hwit : A9Wit (hdRo7A9ExclAux_rho hh f d hh' f' d' σ) i j) : False := by
  obtain ⟨a, ha, haz⟩ := a3_exists_perm hD.hfr hD.h3 σ
  have haP : A3P 3 9 θ z a := ⟨σ, ha, haz⟩
  have haH : a ∈ H := hD.hPH a haP
  have haA : a ∈ A := hD.hHA haH
  have hrA : r ∈ A := hD.hHA hrH
  have hrA' : r' ∈ A := hD.hHA hr'H
  have h1 : A9Lift θ z (a * r') (a9Perm σ ∘ a9Act hh' f' d') :=
    a9Lift_mul (ρ := a9Perm σ) (ρ' := a9Act hh' f' d')
      (a9Lift_perm ha haz) hr' (fun u hu _ => a9Act_mem hhU' hu)
  have h2 : A9Lift θ z (a * r' * a⁻¹)
      ((a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹) :=
    a9Lift_mul (ρ := a9Perm σ ∘ a9Act hh' f' d') (ρ' := a9Perm σ⁻¹)
      h1 (a9Lift_perm_inv ha haz) (fun u hu _ => a9Perm_mem σ⁻¹ hu)
  have h3 : A9Lift θ z (r * (a * r' * a⁻¹))
      (a9Act hh f d ∘ ((a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹)) :=
    a9Lift_mul (ρ := a9Act hh f d) (ρ' := (a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹)
      hr h2 (fun u hu _ => a9Perm_mem σ (a9Act_mem hhU' (a9Perm_mem σ⁻¹ hu)))
  have h4 : A9Lift θ z (r * (a * r' * a⁻¹) * r)
      (a9Act hh f d ∘ ((a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹) ∘ a9Act hh f d) :=
    a9Lift_mul (ρ := a9Act hh f d ∘ ((a9Perm σ ∘ a9Act hh' f' d') ∘ a9Perm σ⁻¹))
      (ρ' := a9Act hh f d) h3 hr (fun u hu _ => a9Act_mem hhU hu)
  have h4' : A9Lift θ z (r * (a * r' * a⁻¹) * r)
      (hdRo7A9ExclAux_rho hh f d hh' f' d' σ) := h4
  have hgA : r * (a * r' * a⁻¹) * r ∈ A :=
    A.mul_mem (A.mul_mem hrA (A.mul_mem (A.mul_mem haA hrA') (A.inv_mem haA))) hrA
  exact hW _ hgA _ h4' i j hwit

private def hdRo7A9ExclAux_czrho (hrh hrf : Fin 9 → ZMod 3) (hrd : ZMod 3)
    (hch hcf : Fin 9 → ZMod 3) (hcd : ZMod 3) (σ : Equiv.Perm (Fin 9)) :
    (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3 :=
  a9Act hrh hrf hrd ∘
    ((a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
      a9Perm σ⁻¹) ∘
    a9Act hrh hrf hrd

private theorem hdRo7A9ExclAux_cz_wit
    (hD : A3LinData 3 9 V θ z H A)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    {hrh hrf : Fin 9 → ZMod 3} {hrd : ZMod 3} {r : V ≃ₗ[ZMod 3] V}
    (hrH : r ∈ H) (hr : A9Real θ z hrh hrf hrd r) (hrhU : hrh ∈ a3Aug 3 9)
    {hch hcf : Fin 9 → ZMod 3} {hcd : ZMod 3} {c : V ≃ₗ[ZMod 3] V}
    (hcH : c ∈ H) (hcreal : A9Real θ z hch hcf hcd c) (hchU : hch ∈ a3Aug 3 9)
    (σ : Equiv.Perm (Fin 9)) (i j : Fin 9)
    (hwit : A9Wit (hdRo7A9ExclAux_czrho hrh hrf hrd hch hcf hcd σ) i j) : False := by
  obtain ⟨a, ha, haz⟩ := a3_exists_perm hD.hfr hD.h3 σ
  have haP : A3P 3 9 θ z a := ⟨σ, ha, haz⟩
  have haH : a ∈ H := hD.hPH a haP
  have haA : a ∈ A := hD.hHA haH
  have hrA : r ∈ A := hD.hHA hrH
  have hcA : c ∈ A := hD.hHA hcH
  have h1 : A9Lift θ z (c * r) (a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) :=
    a9Lift_mul (ρ := a9Act hch hcf hcd) (ρ' := a9Act hrh hrf hrd)
      hcreal hr (fun u hu _ => a9Act_mem hrhU hu)
  have h2 : A9Lift θ z (c * r * c)
      ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd) :=
    a9Lift_mul (ρ := a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) (ρ' := a9Act hch hcf hcd)
      h1 hcreal (fun u hu _ => a9Act_mem hchU hu)
  have h3 : A9Lift θ z (a * (c * r * c))
      (a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) :=
    a9Lift_mul (ρ := a9Perm σ)
      (ρ' := (a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)
      (a9Lift_perm ha haz) h2
      (fun u hu _ => a9Act_mem hchU (a9Act_mem hrhU (a9Act_mem hchU hu)))
  have h4 : A9Lift θ z (a * (c * r * c) * a⁻¹)
      ((a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
        a9Perm σ⁻¹) :=
    a9Lift_mul (ρ := a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘
      a9Act hch hcf hcd)) (ρ' := a9Perm σ⁻¹)
      h3 (a9Lift_perm_inv ha haz) (fun u hu _ => a9Perm_mem σ⁻¹ hu)
  have h5 : A9Lift θ z (r * (a * (c * r * c) * a⁻¹))
      (a9Act hrh hrf hrd ∘
        ((a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
          a9Perm σ⁻¹)) :=
    a9Lift_mul (ρ := a9Act hrh hrf hrd)
      (ρ' := (a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
        a9Perm σ⁻¹)
      hr h4
      (fun u hu _ => a9Perm_mem σ (a9Act_mem hchU (a9Act_mem hrhU (a9Act_mem hchU
        (a9Perm_mem σ⁻¹ hu)))))
  have h6 : A9Lift θ z (r * (a * (c * r * c) * a⁻¹) * r)
      (a9Act hrh hrf hrd ∘
        ((a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
          a9Perm σ⁻¹) ∘
        a9Act hrh hrf hrd) :=
    a9Lift_mul (ρ := a9Act hrh hrf hrd ∘
      ((a9Perm σ ∘ ((a9Act hch hcf hcd ∘ a9Act hrh hrf hrd) ∘ a9Act hch hcf hcd)) ∘
        a9Perm σ⁻¹)) (ρ' := a9Act hrh hrf hrd)
      h5 hr (fun u hu _ => a9Act_mem hrhU hu)
  have h6' : A9Lift θ z (r * (a * (c * r * c) * a⁻¹) * r)
      (hdRo7A9ExclAux_czrho hrh hrf hrd hch hcf hcd σ) := h6
  have hgA : r * (a * (c * r * c) * a⁻¹) * r ∈ A :=
    A.mul_mem (A.mul_mem hrA (A.mul_mem (A.mul_mem haA (A.mul_mem (A.mul_mem hcA hrA)
      hcA)) (A.inv_mem haA))) hrA
  exact hW _ hgA _ h6' i j hwit

private def hdRo7A9ExclAux_sigA : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 3 * Equiv.swap 1 4

private def hdRo7A9ExclAux_sigCp : Equiv.Perm (Fin 9) :=
  Equiv.swap 2 6 * Equiv.swap 2 3 * Equiv.swap 5 7

private def hdRo7A9ExclAux_sigD : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

private def hdRo7A9ExclAux_sigE : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 4 * Equiv.swap 1 5

private def hdRo7A9ExclAux_sigF : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 3 5

theorem a9_excl (hD : A3LinData 3 9 V θ z H A)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    (X : A9Class) (hX : X ≠ .cz ∧ X ≠ .ep ∧ X ≠ .em) {r : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H)
    (hr : A9Real θ z (a9H X) (a9F X) (a9D X) r) : False := by
  obtain ⟨hXcz, hXep, hXem⟩ := hX
  cases X with
  | cz => exact hXcz rfl
  | ep => exact hXep rfl
  | em => exact hXem rfl
  | bpm =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigA 0 2 (by decide)
  | bmp =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigA 0 2 (by decide)
  | cm =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigA 0 2 (by decide)
  | cp =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigCp 0 2 (by decide)
  | d =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigD 0 4 (by decide)
  | e =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigE 0 2 (by decide)
  | f =>
      exact hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide)
        hrH hr (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigF 0 1 (by decide)

theorem a9_excl_mix (hD : A3LinData 3 9 V θ z H A)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    {r r' : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H) (hr : A9Real θ z a9T a9T 2 r) (hr'H : r' ∈ H)
    (hr' : A9Real θ z a9Tn a9Tn 2 r') : False :=
  hdRo7A9ExclAux_conj_wit hD hW hrH hr (by rw [mem_a3Aug]; decide) hr'H hr'
    (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigA 0 2 (by decide)

theorem a9_excl_cz (hD : A3LinData 3 9 V θ z H A)
    (hW : ∀ g ∈ A, ∀ ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3,
      A9Lift θ z g ρ → ∀ a b : Fin 9, ¬ A9Wit ρ a b)
    {r c : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H) (hr : A9Real θ z a9T a9T 2 r) (hcH : c ∈ H)
    (hc : A9Real θ z 0 0 2 c) : False :=
  hdRo7A9ExclAux_cz_wit hD hW hrH hr (by rw [mem_a3Aug]; decide) hcH hc
    (by rw [mem_a3Aug]; decide) hdRo7A9ExclAux_sigA 0 2 (by decide)

end CFSG.StandardType.HdRo7A3.Small
