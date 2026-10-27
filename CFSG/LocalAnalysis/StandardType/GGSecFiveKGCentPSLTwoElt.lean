module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl

import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.KGCentPSL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.SeitzReduction.LinearPilot

private theorem fix_blockSL_of_fix_pairs {K : Type} [Field K] {n : ℕ}
    {β : MulAut (projectiveSL n K)} {J : Finset (Fin n)}
    (h : ∀ (a b : Fin n) (hab : a ≠ b), a ∈ J → b ∈ J → ∀ c : K,
      β (proj n K (SpecialLinearGroup.transvection hab c)) =
        proj n K (SpecialLinearGroup.transvection hab c)) :
    ∀ x ∈ blockSL J, β x = x := by
  have hle : blockSL J ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) := by
    rw [blockSL_eq_closure, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
    exact h i j hij hi hj c
  exact fun x hx => hle hx

private theorem exists_gl_scalar_of_conjAut_eq_one {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {B : GL (Fin n) K} (h : conjAut n K B = 1) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u = B :=
  (eq_one_of_conjAut_mul_fieldAut_eq_one hn B 1 (by rw [map_one, mul_one, h])).2

private theorem isDiag_mul_apply_eq {K : Type} [Field K] {n : ℕ} {B : Matrix (Fin n) (Fin n) K}
    (hB : B.IsDiag) (M : Matrix (Fin n) (Fin n) K) (x y : Fin n) :
    (B * M) x y = B x x * M x y := by
  rw [mul_apply, Finset.sum_eq_single x]
  · intro z _ hz
    rw [hB hz.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

private theorem mul_isDiag_apply_eq {K : Type} [Field K] {n : ℕ} {B : Matrix (Fin n) (Fin n) K}
    (hB : B.IsDiag) (M : Matrix (Fin n) (Fin n) K) (x y : Fin n) :
    (M * B) x y = M x y * B y y := by
  rw [mul_apply, Finset.sum_eq_single y]
  · intro z _ hz
    rw [hB hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ y) h

private theorem apply_eq_zero_of_fix_transvection {K : Type} [Field K] {n : ℕ} {A : GL (Fin n) K}
    {x y : Fin n} (hyx : y ≠ x)
    (h : conjAut n K A (proj n K (SpecialLinearGroup.transvection hyx 1)) =
      proj n K (SpecialLinearGroup.transvection hyx 1)) :
    (A : Matrix (Fin n) (Fin n) K) x y = 0 := by
  obtain ⟨μ, hμ⟩ := exists_rel_of_fix_field (A := A) (σ := 1) hyx 1
    (by rw [map_one, mul_one]; exact h)
  by_contra hne
  have h1 := hμ x y
  have h2 := hμ x x
  rw [if_neg hyx.symm, if_neg hyx, add_zero] at h1
  rw [if_neg hyx.symm, if_pos rfl, add_zero] at h2
  have hμ1 : (1 : K) = μ := mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
  rw [← hμ1, one_mul, show ((1 : K ≃+* K) 1) = 1 from rfl, mul_one] at h2
  exact hne (add_left_cancel ((add_zero _).trans h2)).symm

theorem eq_one_of_commute_diag_fix_pairs {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {ι : Type} (D : ι → GL (Fin n) K)
    (hD : ∀ i, ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    {β : MulAut (projectiveSL n K)} {k : ℕ} (hβ : β ^ 2 ^ k = 1)
    (hcomm : ∀ i, conjAut n K (D i) * β = β * conjAut n K (D i))
    (hfix : ∀ (a b : Fin n) (hab : a ≠ b),
      (∀ i, ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a =
        ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b b) →
      ∀ c : K, β (proj n K (SpecialLinearGroup.transvection hab c)) =
        proj n K (SpecialLinearGroup.transvection hab c))
    {J₀ : Finset (Fin n)} (hJ₀ : 3 ≤ J₀.card)
    (hJ₀D : ∀ a ∈ J₀, ∀ b ∈ J₀, ∀ i, ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a =
      ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b b) :
    β = 1 := by
  have hβJ : ∀ x ∈ blockSL J₀, β x = x :=
    fix_blockSL_of_fix_pairs fun a b hab ha hb => hfix a b hab (hJ₀D a ha b hb)
  obtain ⟨A, rfl, hA⟩ := exists_conjAut_eq_of_fix_blockSL hn hJ₀ hβJ
  obtain ⟨j₀, hj₀⟩ : J₀.Nonempty := Finset.card_pos.1 (by omega)
  have hAj : (A : Matrix (Fin n) (Fin n) K) j₀ j₀ = 1 := by
    rw [hA j₀ j₀ (Or.inl hj₀), one_apply_eq]
  have hdne : ∀ i x, ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x x ≠ 0 := by
    intro i x h0
    have h1 := congrFun (congrFun (Units.mul_inv (D i)) x) x
    rw [isDiag_mul_apply_eq (hD i), h0, zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  have hscal : ∀ i, ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u * (A * D i) = D i * A := by
    intro i
    have h1 : conjAut n K (D i * A * (A * D i)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hcomm i, mul_inv_cancel]
    obtain ⟨u, hu⟩ := exists_gl_scalar_of_conjAut_eq_one hn h1
    exact ⟨u, by rw [hu, inv_mul_cancel_right]⟩
  have hrel : ∀ i x y, (A : Matrix (Fin n) (Fin n) K) x y *
      ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y y =
        ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x x *
          (A : Matrix (Fin n) (Fin n) K) x y := by
    intro i x y
    obtain ⟨u, hu⟩ := hscal i
    have hu' : ∀ x y, (u : K) * ((A : Matrix (Fin n) (Fin n) K) x y *
        ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y y) =
          ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x x *
            (A : Matrix (Fin n) (Fin n) K) x y := by
      intro x y
      have h0 : ((GeneralLinearGroup.scalar (Fin n) u * (A * D i) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = ((D i * A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        congrArg Units.val hu
      have h1 := congrFun (congrFun h0 x) y
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h1
      rw [scalar_apply, diagonal_mul, mul_isDiag_apply_eq (hD i), isDiag_mul_apply_eq (hD i)] at h1
      exact h1
    have hu1 : (u : K) = 1 := by
      have h1 := hu' j₀ j₀
      rw [hAj, one_mul, mul_one] at h1
      exact mul_right_cancel₀ (hdne i j₀) (by rw [h1, one_mul])
    rw [← hu' x y, hu1, one_mul]
  have hoff : ∀ x y, x ≠ y → (A : Matrix (Fin n) (Fin n) K) x y = 0 := by
    intro x y hxy
    by_contra hne
    have hdeq : ∀ i, ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y y =
        ((D i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x x := fun i =>
      mul_left_cancel₀ hne (by rw [hrel i x y, mul_comm])
    exact hne (apply_eq_zero_of_fix_transvection hxy.symm (hfix y x hxy.symm hdeq 1))
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, (A : Matrix (Fin n) (Fin n) K) = diagonal d :=
    ⟨fun x => (A : Matrix (Fin n) (Fin n) K) x x, by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq]
      · rw [diagonal_apply_ne _ hxy, hoff x y hxy]⟩
  have hdA : ∀ x, (A : Matrix (Fin n) (Fin n) K) x x = d x := fun x => by
    rw [hd, diagonal_apply_eq]
  obtain ⟨u, hu⟩ := exists_gl_scalar_of_conjAut_eq_one hn (B := A ^ 2 ^ k)
    (by rw [map_pow]; exact hβ)
  have hpow : ∀ x, d x ^ 2 ^ k = (u : K) := by
    intro x
    have h1 : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = scalar (Fin n) (u : K) := by
      rw [← Units.val_pow_eq_pow_val, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
    have h2 := congrFun (congrFun h1 x) x
    rw [hd, diagonal_pow, scalar_apply, diagonal_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h2
    exact h2
  have hu1 : (u : K) = 1 := by
    rw [← hpow j₀, ← hdA, hAj, one_pow]
  have hd1 : ∀ x, d x = 1 := by
    intro x
    have h0 : (d x - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, hpow x, hu1, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).1 h0)
  have hA1 : A = 1 := by
    apply Units.ext
    rw [hd, Units.val_one, (funext hd1 : d = fun _ => 1), diagonal_one]
  rw [hA1, map_one]

end CFSG.StandardType.KGCentPSL

end
