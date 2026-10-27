module

public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Sporadic.HN

open CFSG.OrderReductions.FrattiniAutomorphisms

theorem card_mulAut_eq_card_GL {p d : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    (e : Additive Q ≃+ (Fin d → ZMod p)) :
    Nat.card (MulAut Q) = Nat.card (GL (Fin d) (ZMod p)) := by
  have e1 : MulAut Q ≃ (Additive Q ≃+ Additive Q) := MulEquiv.toAdditive
  have e2 : (Additive Q ≃+ Additive Q) ≃ ((Fin d → ZMod p) ≃+ (Fin d → ZMod p)) :=
    { toFun := fun f => (e.symm.trans f).trans e
      invFun := fun f => (e.trans f).trans e.symm
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp }
  have e3 : ((Fin d → ZMod p) ≃+ (Fin d → ZMod p)) ≃
      ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
    { toFun := fun f =>
        { toFun := f
          map_add' := map_add f
          map_smul' := fun c x => by
            have key : ∀ y : Fin d → ZMod p, c • y = c.val • y := fun y => by
              ext i
              simp [nsmul_eq_mul]
            have h : f (c • x) = c • f x :=
              calc f (c • x) = f (c.val • x) := congrArg f (key x)
                _ = c.val • f x := map_nsmul f _ _
                _ = c • f x := (key (f x)).symm
            exact h
          invFun := f.symm
          left_inv := f.left_inv
          right_inv := f.right_inv }
      invFun := fun f => f.toAddEquiv
      left_inv := fun f => by ext x; rfl
      right_inv := fun f => by ext x; rfl }
  have e4 : ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) ≃ GL (Fin d) (ZMod p) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin d → ZMod p)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm).toEquiv
  exact Nat.card_congr (((e1.trans e2).trans e3).trans e4)

theorem eq_one_of_pow_eq_one {p q e : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hcard : Nat.card P ∣ p ^ e)
    (hGL : ∀ r ≤ e, ¬ q ∣ Nat.card (GL (Fin r) (ZMod p))) {ψ : MulAut P} (hψ : ψ ^ q = 1) :
    ψ = 1 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨-, -, -, -, d, hd, ⟨e'⟩⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  have hde : d ≤ e := by
    have h1 : p ^ d ∣ p ^ e := by
      rw [← hd]
      exact (Subgroup.card_quotient_dvd_card (frattini P)).trans hcard
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1
  set φ := quotientAutomorphism (frattini P)
  have himg : φ ψ = 1 := by
    have h1 : orderOf (φ ψ) ∣ q := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hψ, map_one])
    have h2 : orderOf (φ ψ) ∣ Nat.card (GL (Fin d) (ZMod p)) := by
      rw [← card_mulAut_eq_card_GL e']
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hq).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h2) (hGL d hde)
  have hker : IsPGroup p φ.ker := frattini_automorphism_kernel_isPGroup p hP
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  let y : φ.ker := ⟨ψ, himg⟩
  have h1 : orderOf y ∣ q :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [y, hψ]))
  have h2 : orderOf y ∣ p ^ k := hk ▸ orderOf_dvd_natCard y
  have h3 : orderOf y = 1 := by
    rcases (Nat.dvd_prime hq).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h2)) hqp
  have := congrArg Subtype.val (orderOf_eq_one_iff.1 h3)
  exact this

theorem not_dvd_card_GL {p q r : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)
    (h : ∀ k, 1 ≤ k → k ≤ r → ¬ q ∣ p ^ k - 1) : ¬ q ∣ Nat.card (GL (Fin r) (ZMod p)) := by
  have hp := (Fact.out : p.Prime)
  rw [Matrix.card_GL_field, ZMod.card]
  intro hd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 hd
  have hir : (i : ℕ) < r := i.isLt
  have e : p ^ r - p ^ (i : ℕ) = p ^ (i : ℕ) * (p ^ (r - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hir.le]
  rw [e] at hi
  rcases (Nat.Prime.dvd_mul hq).1 hi with h1 | h1
  · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1))
  · exact h (r - i) (by omega) (by omega) h1

end CFSG.Sporadic.HN
