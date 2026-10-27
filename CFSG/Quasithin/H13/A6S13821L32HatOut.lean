module

public import CFSG.Quasithin.H13.A6S13821e
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.H13.Sp62Over

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin SL3 CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

namespace L32HatOut

@[expose] def tauFun (A : SL3.S) : SL3.S :=
  ⟨Matrix.transpose (Matrix.adjugate (A : Matrix (Fin 3) (Fin 3) (ZMod 2))), by
    rw [Matrix.det_transpose, Matrix.det_adjugate, A.2, one_pow]⟩

theorem tauFun_mul (A B : SL3.S) : tauFun (A * B) = tauFun A * tauFun B := by
  apply Subtype.ext
  change Matrix.transpose (Matrix.adjugate (A.1 * B.1)) =
    Matrix.transpose (Matrix.adjugate A.1) * Matrix.transpose (Matrix.adjugate B.1)
  generalize A.1 = M
  generalize B.1 = N
  exact (congrArg Matrix.transpose (Matrix.adjugate_mul_distrib M N)).trans (Matrix.transpose_mul _ _)

theorem tauFun_one : tauFun 1 = 1 := by
  apply Subtype.ext
  exact (congrArg Matrix.transpose (Matrix.adjugate_one (n := Fin 3) (α := ZMod 2))).trans
    Matrix.transpose_one

theorem tauFun_invol (A : SL3.S) : tauFun (tauFun A) = A := by
  apply Subtype.ext
  change Matrix.transpose (Matrix.adjugate (Matrix.transpose (Matrix.adjugate A.1))) = A.1
  have hdet : A.1.det = 1 := A.2
  generalize A.1 = M at hdet ⊢
  rw [Matrix.adjugate_transpose, Matrix.transpose_transpose, Matrix.adjugate_adjugate, hdet,
    one_pow, one_smul]
  all_goals simp

@[expose] noncomputable def tauE : SL3.S ≃* SL3.S where
  toFun := tauFun
  invFun := tauFun
  left_inv := tauFun_invol
  right_inv := tauFun_invol
  map_mul' := tauFun_mul

theorem tauE_apply (x : SL3.S) : tauE x = tauFun x := rfl

@[expose] noncomputable def tauAut : MulAut SL3.S := tauE

theorem tau_X1_not_conj : ∀ w : SL3.S, ∃ x : SL3.S,
    (InX1 x ∧ ¬ InX1 (w * tauFun x * w⁻¹)) ∨ (¬ InX1 x ∧ InX1 (w * tauFun x * w⁻¹)) := by
  decide +kernel

theorem tau_X2_not_conj : ∀ w : SL3.S, ∃ x : SL3.S,
    (InX2 x ∧ ¬ InX2 (w * tauFun x * w⁻¹)) ∨ (¬ InX2 x ∧ InX2 (w * tauFun x * w⁻¹)) := by
  decide +kernel

theorem eq_of_card_dvd_two {A : Type*} [Group A] [Finite A] (h : Nat.card A ∣ 2) {x y : A}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have hfin : Fintype A := Fintype.ofFinite A
  have hle : Nat.card A ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have h3 : ({1, x, y} : Finset A).card ≤ Fintype.card A := Finset.card_le_univ _
  have hcard : ({1, x, y} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩
  rw [Nat.card_eq_fintype_card] at hle
  omega

theorem inner_of_preserves_gen (σ : MulAut SL3.S) (P : SL3.S → Prop)
    (hP : ∀ w : SL3.S, ∃ x : SL3.S,
      (P x ∧ ¬ P (w * tauFun x * w⁻¹)) ∨ (¬ P x ∧ P (w * tauFun x * w⁻¹)))
    (hσ : ∀ x : SL3.S, P x ↔ P (σ x)) : σ ∈ inner SL3.S := by
  classical
  have hPSL : IsPSL 3 2 1 SL3.S := isPSL_three_two_iff.mpr ⟨MulEquiv.refl _⟩
  have hO2 : Nat.card (Outer SL3.S) ∣ 2 := card_outer_dvd_two_of_l32 hPSL
  by_contra hσin
  have hτq : (QuotientGroup.mk tauAut : Outer SL3.S) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp h
    have hfix : ∀ x : SL3.S, tauFun x = s * x * s⁻¹ := by
      intro x
      have := congrArg (fun f : MulAut SL3.S => f x) hs
      simpa [tauAut, MulAut.conj_apply, tauE_apply] using this.symm
    obtain ⟨x, hx⟩ := hP s⁻¹
    have hid : s⁻¹ * tauFun x * (s⁻¹)⁻¹ = x := by
      rw [hfix x]
      group
    rw [hid] at hx
    tauto
  have hσq : (QuotientGroup.mk σ : Outer SL3.S) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hσin
  have heq : (QuotientGroup.mk σ : Outer SL3.S) = QuotientGroup.mk tauAut :=
    eq_of_card_dvd_two hO2 hσq hτq
  rw [QuotientGroup.eq] at heq
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp heq
  have hτσ : ∀ y : SL3.S, tauFun y = σ (u * y * u⁻¹) := by
    intro y
    have h1 : (σ⁻¹ * tauAut) y = u * y * u⁻¹ := by
      rw [← hu]
      simp [MulAut.conj_apply]
    have h2 : σ⁻¹ (tauFun y) = u * y * u⁻¹ := by
      simpa [MulAut.mul_apply, tauAut, tauE_apply] using h1
    have h3 : σ (σ⁻¹ (tauFun y)) = σ (u * y * u⁻¹) := by rw [h2]
    have h4 : σ (σ⁻¹ (tauFun y)) = tauFun y := by simp
    rw [h4] at h3
    exact h3
  have hσx : ∀ x : SL3.S, σ x = tauFun u⁻¹ * tauFun x * (tauFun u⁻¹)⁻¹ := by
    intro x
    have h1 := hτσ (u⁻¹ * x * u⁻¹⁻¹)
    have h2 : u * (u⁻¹ * x * u⁻¹⁻¹) * u⁻¹ = x := by group
    rw [h2] at h1
    rw [← h1, tauFun_mul, tauFun_mul]
    have h3 : tauFun u⁻¹⁻¹ = (tauFun u⁻¹)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← tauFun_mul, inv_inv, mul_inv_cancel, tauFun_one]
    rw [h3]
  obtain ⟨x, hx⟩ := hP (tauFun u⁻¹)
  apply hx.elim
  · rintro ⟨h1, h2⟩
    apply h2
    rw [← hσx x]
    exact (hσ x).mp h1
  · rintro ⟨h1, h2⟩
    apply h1
    exact (hσ x).mpr (by rw [hσx x]; exact h2)

theorem inner_of_preserves_X1 (σ : MulAut SL3.S) (hσ : ∀ x : SL3.S, InX1 x ↔ InX1 (σ x)) :
    σ ∈ inner SL3.S :=
  inner_of_preserves_gen σ (fun x => InX1 x) tau_X1_not_conj hσ

theorem inner_of_preserves_X2 (σ : MulAut SL3.S) (hσ : ∀ x : SL3.S, InX2 x ↔ InX2 (σ x)) :
    σ ∈ inner SL3.S :=
  inner_of_preserves_gen σ (fun x => InX2 x) tau_X2_not_conj hσ

end L32HatOut

end CFSG.Quasithin.H13.A6
