module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType

theorem ggRC_card_le_factorial_of_monomial {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i))
    (hdiag : ∀ a ∈ A, (∀ i, ∃ c : ZMod p, a (f i) = c • f i) → a = 1) :
    Nat.card A ≤ n.factorial := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let σ : A → Equiv.Perm (Fin n) := fun a => (hmon a a.2).choose
  have hσ : ∀ a : A, ∃ c : Fin n → ZMod p,
      (∀ i, c i ≠ 0) ∧
        ∀ i, (a : V ≃ₗ[ZMod p] V) (f i) = c i • f (σ a i) :=
    fun a => (hmon a a.2).choose_spec
  have hinj : Function.Injective σ := by
    intro a b hab
    have hfix : ∀ i, ∃ c : ZMod p,
        ((a⁻¹ * b : A) : V ≃ₗ[ZMod p] V) (f i) = c • f i := by
      intro i
      obtain ⟨ca, hca0, hca⟩ := hσ a
      obtain ⟨cb, hcb0, hcb⟩ := hσ b
      have hz : f i = ca i • ((a : V ≃ₗ[ZMod p] V)⁻¹ (f (σ a i))) := by
        rw [← LinearEquiv.symm_apply_apply (a : V ≃ₗ[ZMod p] V) (f i), hca i,
          LinearEquiv.map_smul]
        rfl
      have hz' : ((a : V ≃ₗ[ZMod p] V)⁻¹ (f (σ a i))) = (ca i)⁻¹ • f i := by
        have hval_ne : (ca i).val ≠ 0 := (ZMod.val_ne_zero (ca i)).2 (hca0 i)
        have hval_lt : (ca i).val < p := ZMod.val_lt (ca i)
        have hnotdvd : ¬ p ∣ (ca i).val := by
          intro hdvd
          have h0 : (ca i).val = 0 := by
            have h1 := Nat.mod_eq_zero_of_dvd hdvd
            rwa [Nat.mod_eq_of_lt hval_lt] at h1
          exact hval_ne h0
        have hcop : Nat.Coprime (ca i).val p := by
          rw [Nat.coprime_comm]
          exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hnotdvd
        have hcancel : ca i * (ca i)⁻¹ = 1 := by
          calc ca i * (ca i)⁻¹
              = ((ca i).val : ZMod p) * (((ca i).val : ZMod p))⁻¹ := by
                rw [ZMod.natCast_zmod_val (ca i)]
            _ = 1 := ZMod.coe_mul_inv_eq_one (ca i).val hcop
        have hcancel' : (ca i)⁻¹ * ca i = 1 := by
          rw [mul_comm]
          exact hcancel
        rw [hz, smul_smul, hcancel', one_smul]
      refine ⟨cb i * (ca i)⁻¹, ?_⟩
      calc
        ((a⁻¹ * b : A) : V ≃ₗ[ZMod p] V) (f i)
            = cb i • ((a : V ≃ₗ[ZMod p] V)⁻¹ (f (σ a i))) := by
              rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, hcb i,
                LinearEquiv.map_smul, ← hab]
        _ = cb i • ((ca i)⁻¹ • f i) := by rw [hz']
        _ = (cb i * (ca i)⁻¹) • f i := (mul_smul _ _ _).symm
    have h1 : a⁻¹ * b = 1 := by
      apply Subtype.ext
      simpa using hdiag ((a⁻¹ * b : A) : V ≃ₗ[ZMod p] V) (a⁻¹ * b : A).2 hfix
    have h2 : b = a := by
      have h := congrArg (fun x : A => a * x) h1
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h
      exact h
    exact h2.symm
  calc
    Nat.card A ≤ Nat.card (Equiv.Perm (Fin n)) := Nat.card_le_card_of_injective σ hinj
    _ = n.factorial := by rw [Nat.card_perm, Nat.card_fin]

end CFSG.StandardType
