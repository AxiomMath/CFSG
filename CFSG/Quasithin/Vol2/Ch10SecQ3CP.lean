module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CO
public import CFSG.Quasithin.Vol2.Ch10SecQ3CA
public import CFSG.Quasithin.Vol2.Ch10SecQ3CB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

variable {F : Type} [Field F]

theorem ringEquiv_iterate_add (σ : F ≃+* F) (k : ℕ) (x y : F) :
    (⇑σ)^[k] (x + y) = (⇑σ)^[k] x + (⇑σ)^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, map_add, ih]

theorem ringEquiv_iterate_one (σ : F ≃+* F) (k : ℕ) : (⇑σ)^[k] 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_one, ih]

theorem dU_pow (a : Fˣ) (k : ℕ) : dU a ^ k = dU (a ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, dU_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, dU_mul]

theorem antidiag_conj_dU {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (h1 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (m : Fˣ) : g * dU m * g⁻¹ = dU m⁻¹ := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact g.2
  rw [h0, h1] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_dU,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, h0, h1,
      Units.val_inv_eq_inv_val]
  · linear_combination ((m : F))⁻¹ * hdet
  · linear_combination (m : F) * hdet

theorem eq_one_of_torus [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) {r : ℕ} (hr : Odd r)
    (hrq : Nat.Coprime r (2 ^ n - 1)) (hαr : α ^ r = 1)
    (hT : ∀ l : Fˣ, ∃ l' : Fˣ, α (dU l) = dU l')
    (hC : ∀ l : Fˣ, α (α (dU l) * (dU l)⁻¹) = α (dU l) * (dU l)⁻¹) : α = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨σ, g, hα⟩ := factAutSL2Char2_holds F n hF α
  set s : Fˣ →* Fˣ := Units.map σ.toRingHom.toMonoidHom with hs
  have hsv : ∀ l : Fˣ, ((s l : Fˣ) : F) = σ l := fun l => rfl
  have hαd : ∀ l : Fˣ, α (dU l) = g * dU (s l) * g⁻¹ := fun l => by rw [hα, map_dU]
  have h8 : 4 < Nat.card F := by
    rw [hF]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨x₀, hx0, hx1⟩ : ∃ x : F, x ≠ 0 ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    exact absurd (card_le_four h2 fun x h0 h1 => absurd (hno x h0) h1) (by omega)
  have hμ : ((s (Units.mk0 x₀ hx0) : Fˣ) : F) ≠ (((s (Units.mk0 x₀ hx0))⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val]
    intro h
    have h3 : ((s (Units.mk0 x₀ hx0) : Fˣ) : F) * ((s (Units.mk0 x₀ hx0) : Fˣ) : F) = 1 := by
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ (s (Units.mk0 x₀ hx0)).ne_zero
    have h4 : (((s (Units.mk0 x₀ hx0) : Fˣ) : F) + 1) *
        (((s (Units.mk0 x₀ hx0) : Fˣ) : F) + 1) = 0 := by
      linear_combination h3 + (((s (Units.mk0 x₀ hx0) : Fˣ) : F) + 1) * h2
    have h5 : σ x₀ = σ 1 := by
      rw [map_one]
      exact (by linear_combination (mul_self_eq_zero.mp h4) - h2 :
        ((s (Units.mk0 x₀ hx0) : Fˣ) : F) = 1)
    exact hx1 (σ.injective h5)
  obtain ⟨l', hl'⟩ := hT (Units.mk0 x₀ hx0)
  have hg : g * dU (s (Units.mk0 x₀ hx0)) = dU l' * g := by
    rw [hαd] at hl'
    rw [← hl']
    group
  rcases diag_or_antidiag hμ hg with ⟨a, rfl⟩ | ⟨h0, h1⟩
  ·
    have hαd' : ∀ l : Fˣ, α (dU l) = dU (s l) := fun l => by
      rw [hαd, dU_mul, dU_inv, dU_mul, mul_comm a, mul_assoc, mul_inv_cancel, mul_one]
    have hσ : σ = RingEquiv.refl F := by
      by_contra hne
      obtain ⟨y, hy0, hy⟩ := factFieldAutQuot_holds F σ hne
      apply hy
      have hc := hC (Units.mk0 y hy0)
      rw [hαd', dU_inv, dU_mul, hαd'] at hc
      have hc' := congrArg (fun u : Fˣ => (u : F)) (dU_injective hc)
      simp only [hsv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at hc'
      rw [div_eq_mul_inv]
      exact hc'
    subst hσ
    have hconj : α = MulAut.conj (dU a) := by
      ext x
      rw [hα, MulAut.conj_apply]
      congr 2
    have hcen : dU a ^ r ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [hconj, ← map_pow] at hαr
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) => φ x) hαr
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [center_sl2_eq_bot, Subgroup.mem_bot, dU_pow] at hcen
    have har : a ^ r = 1 := dU_injective (hcen.trans dU_one.symm)
    have hcu : Fintype.card Fˣ = 2 ^ n - 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
    have hq : a ^ (2 ^ n - 1) = 1 := hcu ▸ pow_card_eq_one
    have ha1 : a = 1 := by
      have : a ^ Nat.gcd r (2 ^ n - 1) = 1 := pow_gcd_eq_one.mpr ⟨har, hq⟩
      rwa [Nat.Coprime.gcd_eq_one hrq, pow_one] at this
    rw [hconj, ha1, dU_one, map_one]
  ·
    have hanti : ∀ l : Fˣ, α (dU l) = dU (s l)⁻¹ := fun l => by
      rw [hαd, antidiag_conj_dU h0 h1]
    have hev : ∀ (j : ℕ) (l : Fˣ), ∃ m : Fˣ, (α ^ (2 * j)) (dU l) = dU m ∧
        (m : F) = (⇑σ)^[2 * j] (l : F) := by
      intro j l
      induction j with
      | zero => exact ⟨l, by simp, rfl⟩
      | succ j ih =>
        obtain ⟨m, hm, hmv⟩ := ih
        refine ⟨s (s m), ?_, ?_⟩
        · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ', pow_succ', MulAut.mul_apply,
            MulAut.mul_apply, hm, hanti, hanti, map_inv, inv_inv]
        · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Function.iterate_succ_apply',
            Function.iterate_succ_apply', ← hmv]
          rfl
    obtain ⟨j, rfl⟩ := hr
    have hinv : ∀ x : F, x ≠ 0 → (⇑σ)^[2 * j + 1] x = x⁻¹ := by
      intro x hx
      obtain ⟨m, hm, hmv⟩ := hev j (Units.mk0 x hx)
      rw [Units.val_mk0] at hmv
      have h1 := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) =>
        φ (dU (Units.mk0 x hx))) hαr
      simp only [MulAut.one_apply] at h1
      rw [pow_succ', MulAut.mul_apply, hm, hanti] at h1
      have h2' := congrArg (fun u : Fˣ => (u : F)) (dU_injective h1)
      simp only [Units.val_inv_eq_inv_val, hsv, Units.val_mk0] at h2'
      rw [Function.iterate_succ_apply', ← hmv, ← h2', inv_inv]
    have hq : ∀ x : F, x ≠ 0 → x ≠ 1 → x ^ 2 + x + 1 = 0 := by
      intro x hx0 hx1
      have hx1' : x + 1 ≠ 0 := fun h => hx1 (by linear_combination h - h2)
      have e1 := hinv (x + 1) hx1'
      rw [ringEquiv_iterate_add, ringEquiv_iterate_one, hinv x hx0] at e1
      have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
      have hyy : (x + 1) * (x + 1)⁻¹ = 1 := mul_inv_cancel₀ hx1'
      linear_combination x * hyy + x * (x + 1) * e1 - (x + 1) * hxx
    exact absurd (card_le_four h2 hq) (by omega)

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
