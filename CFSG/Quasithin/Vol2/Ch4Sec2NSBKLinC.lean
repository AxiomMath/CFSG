module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

theorem gl2_pair_involutions (σ τ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hστ : (σ * τ) * (σ * τ) = 1) : σ = 1 ∨ τ = 1 ∨ σ = τ := by
  revert σ τ
  decide

private theorem gl2_fourth_power_one (D : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (h : (D * D) * (D * D) = 1) : D * D = 1 := by
  revert D
  decide

private theorem gl2_sq_of_two_power_aux (e : ℕ) :
    ∀ D : Matrix (Fin 2) (Fin 2) (ZMod 2), D ^ 2 ^ e = 1 → D * D = 1 := by
  induction e with
  | zero =>
    intro D hD
    rw [pow_zero, pow_one] at hD
    rw [hD, one_mul]
  | succ k ih =>
    intro D hD
    have e2 : (D * D) ^ 2 ^ k = D ^ 2 ^ (k + 1) := by
      rw [pow_succ, mul_comm (2 ^ k) 2, pow_mul, sq]
    have h2 : (D * D) ^ 2 ^ k = 1 := by
      rw [e2]
      exact hD
    exact gl2_fourth_power_one D (ih (D * D) h2)

theorem gl2_sq_of_two_power {D : Matrix (Fin 2) (Fin 2) (ZMod 2)} {e : ℕ} (h : D ^ 2 ^ e = 1) :
    D * D = 1 :=
  gl2_sq_of_two_power_aux e D h

theorem exists_addEquiv_factor {E W A : Type*} [AddCommGroup E] [AddCommGroup W] [AddCommGroup A]
    [Finite W] [Finite A] (w : E →+ W) (hw : Function.Surjective w) (a : E →+ A)
    (hker : ∀ x, w x = 0 ↔ a x = 0) (hcard : Nat.card W = Nat.card A) :
    ∃ f : W ≃+ A, ∀ x, a x = f (w x) := by
  have hle : w.ker ≤ a.ker := fun x hx =>
    AddMonoidHom.mem_ker.2 ((hker x).1 (AddMonoidHom.mem_ker.1 hx))
  obtain ⟨f0, hf0⟩ : ∃ f0 : W →+ A, ∀ x, f0 (w x) = a x := by
    refine ⟨(QuotientAddGroup.lift w.ker a hle).comp
      (QuotientAddGroup.quotientKerEquivOfSurjective w hw).symm.toAddMonoidHom, fun x => ?_⟩
    have hx : (QuotientAddGroup.quotientKerEquivOfSurjective w hw).symm (w x) =
        (x : E ⧸ w.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    show QuotientAddGroup.lift w.ker a hle
      ((QuotientAddGroup.quotientKerEquivOfSurjective w hw).symm (w x)) = a x
    rw [hx]
    rfl
  have hinj : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hw y
    rw [hf0] at hy
    exact (hker x).2 hy
  have hbij : Function.Bijective (f0 : W → A) :=
    (Nat.bijective_iff_injective_and_card (f0 : W → A)).2 ⟨hinj, hcard⟩
  exact ⟨AddEquiv.ofBijective f0 hbij, fun x => (hf0 x).symm⟩

end CFSG.Quasithin.H13.Ch4.NSB
