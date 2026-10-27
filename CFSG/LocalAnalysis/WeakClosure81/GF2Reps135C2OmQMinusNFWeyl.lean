module

public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBRealize

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

@[expose] def omqnfRealizes (m : ℕ) (w : (coxeterMatrix (isFiniteType_cartanB m)).Group)
    (π : Equiv.Perm (Fin m)) (s : Fin m → ℤ) : Prop :=
  ∀ γ, toStdB m (weylAction (isFiniteType_cartanB m) w γ) =
    fun b => s (π.symm b) * toStdB m γ (π.symm b)

theorem omqnfRealizes_one (m : ℕ) : omqnfRealizes m 1 1 1 := fun γ => by
  rw [map_one, Module.End.one_apply]
  funext b
  change toStdB m γ b = 1 * toStdB m γ b
  rw [one_mul]

theorem omqnfRealizes.congr {m : ℕ} {w : (coxeterMatrix (isFiniteType_cartanB m)).Group}
    {π π' : Equiv.Perm (Fin m)} {s s' : Fin m → ℤ} (h : omqnfRealizes m w π s) (hπ : π = π')
    (hs : s = s') : omqnfRealizes m w π' s' :=
  hπ ▸ hs ▸ h

theorem omqnfRealizes.mul {m : ℕ} {w₁ w₂ : (coxeterMatrix (isFiniteType_cartanB m)).Group}
    {π₁ π₂ : Equiv.Perm (Fin m)} {s₁ s₂ : Fin m → ℤ} (h₁ : omqnfRealizes m w₁ π₁ s₁)
    (h₂ : omqnfRealizes m w₂ π₂ s₂) :
    omqnfRealizes m (w₁ * w₂) (π₁ * π₂) (fun c => s₂ c * s₁ (π₂ c)) := fun γ => by
  rw [weylAction_mul_apply, h₁, h₂]
  funext b
  simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  ring

theorem omqnfRealizes.inv {m : ℕ} {w : (coxeterMatrix (isFiniteType_cartanB m)).Group}
    {π : Equiv.Perm (Fin m)} {s : Fin m → ℤ} (h : omqnfRealizes m w π s) (hs : SpIsSign s) :
    omqnfRealizes m w⁻¹ π⁻¹ (fun c => s (π.symm c)) := fun γ => by
  have key := h (weylAction (isFiniteType_cartanB m) w⁻¹ γ)
  rw [weylAction_apply_inv_apply] at key
  funext b
  have e := congrFun key (π b)
  simp only [Equiv.symm_apply_apply] at e
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [e, ← mul_assoc, hs.mul_self, one_mul]

theorem omqnfRealizes_simple_of_lt {m : ℕ} {k : Fin m} (h : k.val + 1 < m) :
    omqnfRealizes m ((coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem.simple k)
      (Equiv.swap k ⟨k.val + 1, h⟩) 1 := fun γ => by
  rw [weylAction_simple, toStdB_reflection_of_lt m h]
  funext b
  simp [Equiv.symm_swap]

theorem omqnfRealizes_simple_of_not_lt {m : ℕ} {k : Fin m} (h : ¬ k.val + 1 < m) :
    omqnfRealizes m ((coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem.simple k) 1
      (spSgn k) := fun γ => by
  rw [weylAction_simple, toStdB_reflection, stdReflB_of_not_lt m h]
  funext b
  change (if b = k then -1 else 1) * toStdB m γ b = spSgn k b * toStdB m γ b
  rfl

theorem omqnfRealizes_unique {m : ℕ} {w : (coxeterMatrix (isFiniteType_cartanB m)).Group}
    {π π' : Equiv.Perm (Fin m)} {s s' : Fin m → ℤ} (h : omqnfRealizes m w π s)
    (h' : omqnfRealizes m w π' s') (hs : SpIsSign s) : π = π' ∧ s = s' := by
  have key : ∀ a, π a = π' a ∧ s a = s' a := by
    intro a
    let γ : Fin m → ℤ := ofStdB m (Pi.single a 1)
    have hγ : toStdB m γ = Pi.single a 1 := toStdB_ofStdB m _
    have heq : s (π.symm (π a)) * toStdB m γ (π.symm (π a)) =
        s' (π'.symm (π a)) * toStdB m γ (π'.symm (π a)) := by
      have h1 := congrFun (h γ) (π a)
      have h2 := congrFun (h' γ) (π a)
      exact h1.symm.trans h2
    rw [hγ] at heq
    simp only [Equiv.symm_apply_apply, Pi.single_eq_same] at heq
    by_cases hd : π'.symm (π a) = a
    · have hπ : π a = π' a := by
        have := congrArg π' hd
        rwa [Equiv.apply_symm_apply] at this
      refine ⟨hπ, ?_⟩
      rw [hd] at heq
      simp only [Pi.single_eq_same] at heq
      omega
    · exfalso
      have hz : s a = 0 := by
        have hsingle : (Pi.single a (1 : ℤ) : Fin m → ℤ) (π'.symm (π a)) = 0 := by
          rw [Pi.single_apply, if_neg hd]
        rw [hsingle] at heq
        simp only [mul_zero] at heq
        omega
      rcases hs a with h1 | h1 <;> omega
  exact ⟨Equiv.ext fun a => (key a).1, funext fun a => (key a).2⟩

end CFSG.LocalAnalysis.WeakClosure81
