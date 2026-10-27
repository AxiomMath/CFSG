module

public import CFSG.LieType.Universal.Spin.Twisted.Frame
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWitness
public import CFSG.LieType.Universal.Spin.Chevalley.Odd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.StandardType

@[expose] def omqnfFrame (n : ℕ) (K : Type*) [Field K] : Fin (n - 1) ⊕ Fin (n - 1) → Vm n K :=
  Sum.elim (eVec n (K := K)) (fVec n (K := K))

@[expose] def omqnfActs (n : ℕ) {K : Type*} [Field K] (b c : K) (π : Equiv.Perm (Fin (n - 1)))
    (s : Fin (n - 1) → ℤ) (T : Vm n K ≃ₗ[K] Vm n K) : Prop :=
  (∀ x, T (omqnfFrame n K x) = omqnfFrame n K (spMonoPerm π s x)) ∧
  ∀ p, T (planeVec n p) = planeVec n (if ∏ a, s a = 1 then p else planeRefl b c planeOne p)

private theorem omqnfac_prod_sign {m : ℕ} {s : Fin m → ℤ} (hs : SpIsSign s) :
    ∏ a, s a = 1 ∨ ∏ a, s a = -1 := by
  refine Finset.prod_induction s (fun x => x = 1 ∨ x = -1) ?_ (Or.inl rfl) (fun a _ => hs a)
  rintro x y (hx | hx) (hy | hy) <;> simp [hx, hy]

theorem omqnfActs_one (n : ℕ) {K : Type*} [Field K] (b c : K) :
    omqnfActs n b c (1 : Equiv.Perm (Fin (n - 1))) (1 : Fin (n - 1) → ℤ)
      (1 : Vm n K ≃ₗ[K] Vm n K) := by
  refine ⟨fun x => ?_, fun p => ?_⟩
  · rw [spMonoPerm_one]
    rfl
  · simp

theorem omqnfActs.mul {n : ℕ} {K : Type*} [Field K] {b c : K} {π₁ π₂ : Equiv.Perm (Fin (n - 1))}
    {s₁ s₂ : Fin (n - 1) → ℤ} {T₁ T₂ : Vm n K ≃ₗ[K] Vm n K}
    (h₁ : omqnfActs n b c π₁ s₁ T₁) (h₂ : omqnfActs n b c π₂ s₂ T₂) (hs₁ : SpIsSign s₁)
    (hs₂ : SpIsSign s₂) :
    omqnfActs n b c (π₁ * π₂) (fun a => s₂ a * s₁ (π₂ a)) (T₁ * T₂) := by
  refine ⟨fun x => ?_, fun p => ?_⟩
  · rw [spMonoPerm_mul hs₁ hs₂, LinearEquiv.mul_apply, h₂.1, h₁.1]
    rfl
  · rw [LinearEquiv.mul_apply, h₂.2, h₁.2]
    have hprod : ∏ a, s₂ a * s₁ (π₂ a) = (∏ a, s₂ a) * ∏ a, s₁ a := by
      rw [Finset.prod_mul_distrib, Equiv.prod_comp π₂ s₁]
    rw [hprod]
    rcases omqnfac_prod_sign hs₁ with h1 | h1 <;> rcases omqnfac_prod_sign hs₂ with h2 | h2 <;>
      simp [h1, h2, planeRefl_planeRefl planeNorm_planeOne_ne_zero]

theorem omqnfActs.mul_self_eq_one {n : ℕ} {K : Type*} [Field K] {b c : K}
    {π : Equiv.Perm (Fin (n - 1))} {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K}
    (h : omqnfActs n b c π s T) (hσ : spMonoPerm π s * spMonoPerm π s = 1) : T * T = 1 := by
  have key : ∀ x, T (T (omqnfFrame n K x)) = omqnfFrame n K x := by
    intro x
    rw [h.1, h.1]
    have := congrArg (fun p : Equiv.Perm _ => p x) hσ
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
    rw [this]
  have hpl : ∀ p, T (T (planeVec n p)) = planeVec n p := by
    intro p
    rw [h.2, h.2]
    split_ifs
    · rfl
    · rw [planeRefl_planeRefl planeNorm_planeOne_ne_zero]
  have hTT : ∀ j : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2, T (T (Pi.single j 1)) = Pi.single j 1 := by
    intro j
    rcases j with a | a | t
    · exact key (Sum.inl a)
    · exact key (Sum.inr a)
    · have hpl' : (Pi.single (Sum.inr (Sum.inr t)) (1 : K) : Vm n K) =
          planeVec n (Pi.single t 1) := by
        funext a
        rcases a with i | i | s <;> simp [planeVec, Pi.single_apply, Sum.inr.injEq]
      rw [hpl']
      exact hpl _
  ext v : 1
  have hlin : ((T * T : Vm n K ≃ₗ[K] Vm n K) : Vm n K →ₗ[K] Vm n K) = LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Vm n K) = x • Pi.single i 1 := by
      rw [← Pi.single_smul']
      simp
    rw [hx]
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_smul, hTT, LinearMap.id_apply]
  exact congrArg (fun f : Vm n K →ₗ[K] Vm n K => f v) hlin

end CFSG.LocalAnalysis.WeakClosure81
